from cegis import Cegis
from circuit_encoding import CircuitEncoding
import functools
import pono
import smt_switch.primops as pops
from smt_switch.sortkinds import BOOL, BV

class CircuitSynth:
    def __init__(self, nodes, types, ops, spec_func, num_cycles):
        self.enc = CircuitEncoding(nodes, types, ops)
        self.ur = pono.Unroller(nodes.fts)
        self.solver = nodes.fts.solver
        synth_base = self.enc.P_wfp

        P_conn = []
        for n in range(num_cycles + 1):
            P_conn.append(self.ur.at_time(self.enc.P_conn, n))
        P_conn = functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), P_conn)

        P_state = [self.ur.at_time(nodes.fts.init, 0)]
        for n in range(num_cycles):
            P_state.append(self.ur.at_time(nodes.fts.trans, n))
        P_state = functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), P_state)

        P_spec = []
        input_vars = []
        for n in range(num_cycles + 1):
            input_vars.append(tuple(self.ur.at_time(var, n) for var in self.enc.input_vars))
            spec_outputs = spec_func(tuple(input_vars))
            circuit_outputs = tuple(self.ur.at_time(var, n) for var in self.enc.output_vars)
            outputs_equal = tuple(self.solver.make_term(pops.Equal, so, co) for so, co in zip(spec_outputs, circuit_outputs))
            P_spec.append(functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), outputs_equal))
        P_spec = functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), P_spec)

        synth_constrain = functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), [P_conn, P_state, P_spec])
        verify = self.solver.make_term(pops.Implies, functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), [self.enc.P_wfp, P_conn, P_state]), P_spec)

        dependent_vars = []
        for n in range(num_cycles + 1):
            for var in self.enc.D_vars:
                dependent_vars.append(self.ur.at_time(var, n))

        input_vars_flat = tuple(var for vars_ in input_vars for var in vars_)
        self.cegis = Cegis(self.solver, synth_base, synth_constrain, verify, self.enc.E_vars, input_vars_flat, dependent_vars)


    def run(self):
        res = self.cegis.run()
        if res is None:
            return None
        op_input_lvars = tuple(tuple(res[lvar] for lvar in input_lvars) for input_lvars in self.enc.op_input_lvars)
        op_output_lvars = tuple(tuple(res[lvar] for lvar in output_lvars) for output_lvars in self.enc.op_output_lvars)
        output_lvars = tuple(res[lvar] for lvar in self.enc.output_lvars)
        return self.enc.input_lvars, op_input_lvars, op_output_lvars, output_lvars


import smt_switch as ss
import pono
from nodes import Nodes
s = ss.create_btor_solver(False)
s.set_opt('produce-models', 'true')
s.set_opt('incremental', 'true')
fts = pono.FunctionalTransitionSystem(s)
n = Nodes(fts)
def f(inputs):
    if len(inputs) == 1:
        return (s.make_term(0, s.make_sort(BV, 2)),)
    return functools.reduce(lambda a,b: (s.make_term(pops.BVAdd, a[0], b[0]),), inputs)
    
cs = CircuitSynth(n, ((2,),(2,)), (n.Add(N = 2), n.Register(N = 2, init = 0)), f, 2)
print(cs.run())


