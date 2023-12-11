import functools
from itertools import combinations
import smt_switch.primops as pops
from smt_switch.sortkinds import BOOL, BV

class CircuitEncoding:
    def __init__(self, nodes, types, ops):
        if not isinstance(types, tuple):
            raise TypeError(f"CircuitSynth input types should be a tuple, got {type(types)}")
        if not isinstance(types[0], tuple):
            raise TypeError(f"CircuitSynth input types[0] should be a tuple, got {type(types[0])}")
        if not isinstance(types[1], tuple):
            raise TypeError(f"CircuitSynth input types[1] should be a tuple, got {type(types[1])}")
        if not isinstance(ops, tuple):
            raise TypeError(f"CircuitSynth input ops should be a tuple, got {type(ops)}")
        for op in ops:
            if not isinstance(op, (nodes.SeqNode, nodes.CombNode)):
                raise TypeError(f"CircuitSynth input ops should have elements of type SeqNode or CombNode, got {type(op)}")

        self.nodes = nodes
        self.fts = nodes.fts
        self.solver = nodes.fts.solver
        self.types = types
        self.ops = ops

        self.num_inputs = len(types[0])
        self.num_outputs = len(types[1])
        self.num_op_outputs = sum(len(op.types[1]) for op in ops)
        self.num_lines = self.num_inputs + self.num_op_outputs
        self.lvar_width = (self.num_lines - 1).bit_length()
        BV_LVAR = self.solver.make_sort(BV, self.lvar_width)

        self.input_lvars = tuple(self.solver.make_term(i, BV_LVAR) for i in range(self.num_inputs))
        self.op_input_lvars = tuple(tuple(self.solver.make_symbol(f"op_input_lvar[{i}][{j}]", BV_LVAR) for j in range(len(op.types[0]))) for i,op in enumerate(ops))
        self.op_output_lvars = tuple(tuple(self.solver.make_symbol(f"op_output_lvar[{i}][{j}]", BV_LVAR) for j in range(len(op.types[1]))) for i,op in enumerate(ops))
        self.output_lvars = tuple(self.solver.make_symbol(f"output_lvar[{i}]", BV_LVAR) for i in range(self.num_outputs))

        self.input_vars = tuple(self.fts.make_inputvar(f"input_var[{i}]", self.solver.make_sort(BV, N)) for i,N in enumerate(types[0]))
        self.op_input_vars = tuple(tuple(self.fts.make_inputvar(f"op_input_var[{i}][{j}]", self.solver.make_sort(BV, N)) for j,N in enumerate(op.types[0])) for i,op in enumerate(ops))
        self.op_output_vars = tuple(op.eval(*input_vars) for op,input_vars in zip(ops, self.op_input_vars))
        self.output_vars = tuple(self.select_var(output_lvar, t) for output_lvar,t in zip(self.output_lvars, types[1]))

        def flatten(tps):
            return tuple(x for tp in tps for x in tp)
        self.E_vars = flatten(self.op_input_lvars) + flatten(self.op_output_lvars) + self.output_lvars
        self.A_vars = self.input_vars
        self.D_vars = flatten(self.op_input_vars) + flatten(op.state_vars for op in ops if isinstance(op, nodes.SeqNode))

    def select_var(self, target_lvar, target_t):
        # dont include non-matching types in the resulting formula
        possible_pairs = []
        for lvar, var, t in zip(self.input_lvars, self.input_vars, self.types[0]):
            if target_t == t:
                possible_pairs.append((lvar, var))

        for output_lvars, output_vars, op in zip(self.op_output_lvars, self.op_output_vars, self.ops):
            for lvar, var, t in zip(output_lvars, output_vars, op.types[1]):
                if target_t == t:
                    possible_pairs.append((lvar, var))

        assert len(possible_pairs) != 0
        res = possible_pairs[0][1]
        for lvar,var in possible_pairs[1:]:
            res = self.solver.make_term(pops.Ite, self.solver.make_term(pops.Equal, target_lvar, lvar), var, res)
        return res

    @property
    def P_acyc(self):
        #the circuit must be acyclic
        BV_LVAR = self.solver.make_sort(BV, self.lvar_width)
        cond = []
        hardcoded_lvars = self.num_inputs
        for input_lvars, output_lvars, op in zip(self.op_input_lvars, self.op_output_lvars, self.ops):
            # the output lvars are increasing by 1
            if isinstance(op, self.nodes.CombNode):
                for input_lvar in input_lvars:
                    cond.append(self.solver.make_term(pops.BVUlt, input_lvar, output_lvars[0]))
            else:
                assert isinstance(op, self.nodes.SeqNode)
                cond.append(self.solver.make_term(pops.Equal, output_lvars[0], self.solver.make_term(hardcoded_lvars, BV_LVAR)))
                hardcoded_lvars += len(output_lvars)
        return functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), cond)

    @property
    def P_lvars_in_range(self):
        #all src lvars must be a valid line number
        BV_LVAR = self.solver.make_sort(BV, self.lvar_width)
        min_lvar = self.solver.make_term(self.num_inputs, BV_LVAR)
        max_lvar = self.solver.make_term(self.num_lines-1, BV_LVAR)
        cond = []
        for out_lvars in self.op_output_lvars:
            for lvar in out_lvars:
                cond.append(self.solver.make_term(pops.BVUge, lvar, min_lvar))
                cond.append(self.solver.make_term(pops.BVUle, lvar, max_lvar))
        return functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), cond)

    @property
    def P_multi_out(self):
        #successive outputs of an op should have lvar values increasing by 1
        cond = [self.solver.make_term(1, self.solver.make_sort(BOOL))]
        BV_LVAR = self.solver.make_sort(BV, self.lvar_width)
        one = self.solver.make_term(1, BV_LVAR)
        for output_lvars in self.op_output_lvars:
            for l,r in zip(output_lvars[:-1], output_lvars[1:]):
                cond.append(self.solver.make_term(pops.Equal, self.solver.make_term(pops.BVAdd, l, one), r))
        return functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), cond)

    @property
    def P_src_lvars_unique(self):
        #all src lvars must be a unique line number
        cond = [self.solver.make_term(1, self.solver.make_sort(BOOL))]
        lvars_all = tuple(lvar for output_lvars in self.op_output_lvars for lvar in output_lvars)
        for a,b in combinations(lvars_all, 2):
            cond.append(self.solver.make_term(pops.Not, self.solver.make_term(pops.Equal, a, b)))
        return functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), cond)

    @property
    def P_well_typed(self):
        #sink lvars can only correspond to source lvars of the same bit width
        cond = []

        #collect sources of each type
        srcs = {}
        for lvar, t in zip(self.input_lvars, self.types[0]):
            srcs.setdefault(t, []).append(lvar)
        for output_lvars,op in zip(self.op_output_lvars, self.ops):
            for lvar, t in zip(output_lvars, op.types[1]):
                srcs.setdefault(t, []).append(lvar)
        
        #constrain sinks of each type
        for lvar, t in zip(self.output_lvars, self.types[1]):
            assert t in srcs
            c = tuple(self.solver.make_term(pops.Equal, lvar, s) for s in srcs[t])
            cond.append(functools.reduce(lambda a,b: self.solver.make_term(pops.Or, a, b), c))

        for input_lvars, op in zip(self.op_input_lvars, self.ops):
            for lvar,t in zip(input_lvars, op.types[0]):
                assert t in srcs
                c = tuple(self.solver.make_term(pops.Equal, lvar, s) for s in srcs[t])
                cond.append(functools.reduce(lambda a,b: self.solver.make_term(pops.Or, a, b), c))
        
        return functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), cond)

    @property
    def P_wfp(self):
        #well formed program
        cond = (self.P_acyc, self.P_lvars_in_range, self.P_multi_out, self.P_src_lvars_unique, self.P_well_typed)
        return functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), cond)

    @property
    def P_conn(self):
        #assert that the op input values are assigned to the corresponding sources
        cond = []
        for input_lvars,input_vars,op in zip(self.op_input_lvars, self.op_input_vars, self.ops):
            for lvar,var,t in zip(input_lvars, input_vars, op.types[0]):
                cond.append(self.solver.make_term(pops.Equal, self.select_var(lvar, t), var))

        return functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), cond)