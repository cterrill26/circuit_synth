import pono
import smt_switch as ss
import smt_switch.primops as ops
from smt_switch.sortkinds import BV


class Nodes:
    def __init__(self, fts, delay_width):
        self.fts = fts
        solver = fts.solver
        self.delay_width = delay_width

        bin_type_func = lambda pargs: ((pargs["N"], pargs["N"]), (pargs["N"],))
        def bin_delay_func(pargs, *delays):
            max_in_delay = solver.make_term(ops.Ite, solver.make_term(ops.BVSgt, delays[0], delays[1]), delays[0], delays[1])
            op_delay = solver.make_term(pargs["delay"], solver.make_sort(BV, delay_width))
            return (solver.make_term(ops.BVAdd, max_in_delay, op_delay),)

        self.Add = self.make_comb("Add", {"N": int, "delay": int}, lambda x, y: (solver.make_term(ops.BVAdd, x, y),), bin_type_func, bin_delay_func)
        self.Sub = self.make_comb("Sub", {"N": int, "delay": int}, lambda x, y: (solver.make_term(ops.BVSub, x, y),), bin_type_func, bin_delay_func)
        self.Mul = self.make_comb("Mul", {"N": int, "delay": int}, lambda x, y: (solver.make_term(ops.BVMul, x, y),), bin_type_func, bin_delay_func)
        self.And = self.make_comb("And", {"N": int, "delay": int}, lambda x, y: (solver.make_term(ops.BVAnd, x, y),), bin_type_func, bin_delay_func)
        self.Or = self.make_comb("Or", {"N": int, "delay": int}, lambda x, y: (solver.make_term(ops.BVOr, x, y),), bin_type_func, bin_delay_func)
        self.Xor = self.make_comb("Xor", {"N": int, "delay": int}, lambda x, y: (solver.make_term(ops.BVXor, x, y),), bin_type_func, bin_delay_func)

        cmp_type_func = lambda pargs: ((pargs["N"], pargs["N"]), (1,))
        def cmp_delay_func(pargs, *delays):
            max_in_delay = solver.make_term(ops.Ite, solver.make_term(ops.BVSgt, delays[0], delays[1]), delays[0], delays[1])
            op_delay = solver.make_term(pargs["delay"], solver.make_sort(BV, delay_width))
            return (solver.make_term(ops.BVAdd, max_in_delay, op_delay),)

        self.Equal = self.make_comb("Equals", {"N": int, "delay": int}, lambda x, y: (solver.make_term(ops.Equal, x, y),), cmp_type_func, cmp_delay_func)
        self.Ult = self.make_comb("Lt", {"N": int, "delay": int}, lambda x, y: (solver.make_term(ops.BVUlt, x, y),), cmp_type_func, cmp_delay_func)
        self.Ugt = self.make_comb("Gt", {"N": int, "delay": int}, lambda x, y: (solver.make_term(ops.BVUgt, x, y),), cmp_type_func, cmp_delay_func)
        self.Ule = self.make_comb("Lte", {"N": int, "delay": int}, lambda x, y: (solver.make_term(ops.BVUle, x, y),), cmp_type_func, cmp_delay_func)
        self.Uge = self.make_comb("Gte", {"N": int, "delay": int}, lambda x, y: (solver.make_term(ops.BVUge, x, y),), cmp_type_func, cmp_delay_func)

        mux_type_func = lambda pargs: ((1, pargs["N"], pargs["N"]), (pargs["N"],))
        def mux_delay_func(pargs, *delays):
            max_in_delay = solver.make_term(ops.Ite, solver.make_term(ops.BVSgt, delays[0], delays[1]), delays[0], delays[1])
            max_in_delay = solver.make_term(ops.Ite, solver.make_term(ops.BVSgt, delays[2], max_in_delay), delays[2], max_in_delay)
            op_delay = solver.make_term(pargs["delay"], solver.make_sort(BV, delay_width))
            return (solver.make_term(ops.BVAdd, max_in_delay, op_delay),)

        self.Mux = self.make_comb("Mux", {"N": int, "delay": int}, lambda s, x, y: (solver.make_term(ops.Ite, s, x, y),), mux_type_func, mux_delay_func)

        def register_eval_func(inst, d):
            BVN = solver.make_sort(BV, inst.pargs["N"])

            reg = fts.make_statevar(f"Register{type(inst).count}", BVN)
            type(inst).count += 1

            fts.constrain_init(solver.make_term(ops.Equal, reg, solver.make_term(inst.pargs["init"], BVN)))
            fts.assign_next(reg, d)
            return (reg,),(reg,)

        register_type_func = lambda pargs: ((pargs["N"],), (pargs["N"],))
        def register_delay_func(pargs, delay):
            delaysort = solver.make_sort(BV, delay_width)
            setup = solver.make_term(pargs["setup"], delaysort)
            delay_with_setup = solver.make_term(ops.BVAdd, delay, setup)
            hold = solver.make_term(pargs["hold"], delaysort)
            delay_without_hold = solver.make_term(ops.BVAdd, delay, solver.make_term(ops.BVNeg, hold))
            return (delay_with_setup,), (delay_without_hold,),(solver.make_term(pargs["output_delay"], delaysort),)

        self.Register = self.make_seq("Register", {"N": int, "init": int, "setup": int, "hold": int, "output_delay": int}, register_eval_func, register_type_func, register_delay_func)


    class Node:
        def __init__(self, **pargs):
            self.pargs = pargs

        def eval(self, *args):
            raise NotImplementedError("Abstract method")
        
        def __call__(self, *args):
            return self.eval(*args)


    class SeqNode(Node):
        def __init__(self, **pargs):
            super().__init__(**pargs)

    class CombNode(Node):
        def __init__(self, **pargs):
            super().__init__(**pargs)

    class SpecNode(Node):
        def __init__(self, **pargs):
            super().__init__(**pargs)
    

    def make_attributes(self, name, params, eval_func, is_stateful, type_func):
        def init(self, **pargs):
            super(type(self), self).__init__(**pargs)
            missing_params = set(params.keys()) - set(pargs.keys())
            if len(missing_params) > 0:
                k = missing_params.pop()
                raise ValueError(f"{name} expects parameter {k} of type {params[k]}")

            for k,v in pargs.items():
                if k not in params:
                    raise ValueError(f"{name} does not expect parameter {k}")
                if not isinstance(v, params[k]):
                    raise TypeError(f"{name} parameter {k} expected to be of type {params[k]}, got {type(v)}")
            
            self.types = type_func(pargs)
            self.name = name

        def to_string(self):
            s = ",".join(f"{k}={self.pargs[k]}" for k in params.keys())
            return f"{name}<{s}>"
        
        def tc_eval_func(self, *args):
            assert all((isinstance(a, ss.Term) and a.get_sort().get_sort_kind() == BV) for a in args)
            expected_in_t = self.types[0]
            expected_out_t = self.types[1]
            actual_in_t = tuple(a.get_sort().get_width() for a in args)
            if not expected_in_t == actual_in_t:
                raise TypeError(f"{self.name} expects input values of type {expected_in_t}, got {actual_in_t}")

            if is_stateful:
                state_vars, out = eval_func(self, *args)
                self.state_vars = state_vars
            else:
                out = eval_func(*args)

            if not isinstance(out, tuple):
                raise TypeError(f"{self.name} expects a tuple output value, got {type(out)}")

            assert all((isinstance(o, ss.Term) and o.get_sort().get_sort_kind() == BV) for o in out)

            actual_out_t = tuple(o.get_sort().get_width() for o in out)
            if not expected_out_t == actual_out_t:
                raise TypeError(f"{self.name} expects output values of type {expected_out_t}, got {actual_out_t}")
            
            return out

        attributes = {
            "__init__": init,
            "__str__": to_string,
            "eval": tc_eval_func
        }

        return attributes
    

    def make_seq(self, name, params, eval_func, type_func, timing_func):
        attributes = self.make_attributes(name, params, eval_func, True, type_func)
        attributes["count"] = 0

        def timing(self, *input_delays):
            assert all((isinstance(i, ss.Term) and i.get_sort().get_sort_kind() == BV) for i in input_delays)
            assert len(input_delays) == len(self.types[0])
            setup, hold, output_delays = timing_func(self.pargs, *input_delays)
            assert all((isinstance(i, ss.Term) and i.get_sort().get_sort_kind() == BV) for i in setup)
            assert all((isinstance(i, ss.Term) and i.get_sort().get_sort_kind() == BV) for i in hold)
            assert all((isinstance(i, ss.Term) and i.get_sort().get_sort_kind() == BV) for i in output_delays)
            assert len(output_delays) == len(setup) == len(hold) == len(self.types[1])
            self.setup = setup
            self.hold = hold
            return output_delays

        attributes["timing"] = timing
        return type(name, (self.SeqNode,), attributes)


    def make_comb(self, name, params, eval_func, type_func, timing_func):
        attributes = self.make_attributes(name, params, eval_func, False, type_func)

        def timing(self, *input_delays):
            assert all((isinstance(i, ss.Term) and i.get_sort().get_sort_kind() == BV) for i in input_delays)
            assert len(input_delays) == len(self.types[0])
            output_delays = timing_func(self.pargs, *input_delays)
            assert all((isinstance(i, ss.Term) and i.get_sort().get_sort_kind() == BV) for i in output_delays)
            assert len(output_delays) == len(self.types[1])
            return output_delays

        attributes["timing"] = timing
        return type(name, (self.CombNode,), attributes)

    def make_spec(self, name, params, spec_func, type_func, timing_func, is_moores):
        attributes = self.make_attributes(name, params, spec_func, False, type_func)
        def timing(self, *input_delays):
            assert all((isinstance(i, ss.Term) and i.get_sort().get_sort_kind() == BV) for i in input_delays)
            assert len(input_delays) == len(self.types[0])
            setup, hold, output_delays = timing_func(self.pargs, *input_delays)
            assert all((isinstance(i, ss.Term) and i.get_sort().get_sort_kind() == BV) for i in setup)
            assert all((isinstance(i, ss.Term) and i.get_sort().get_sort_kind() == BV) for i in hold)
            assert all((isinstance(i, ss.Term) and i.get_sort().get_sort_kind() == BV) for i in output_delays)
            assert len(output_delays) == len(setup) == len(hold) == len(self.types[1])
            self.setup = setup
            self.hold = hold
            return output_delays

        #overwrite the eval function
        def tc_spec_func(self, *args):
            assert all((isinstance(a, ss.Term) and a.get_sort().get_sort_kind() == BV) for a_at_time in args for a in a_at_time)
            expected_in_t = self.types[0]
            expected_out_t = self.types[1]
            actual_in_t = tuple(tuple(a.get_sort().get_width() for a in a_at_time) for a_at_time in args)
            if not all((expected_in_t == actual_in_at_time) for actual_in_at_time in actual_in_t):
                raise TypeError(f"{self.name} expects input values at each timestep of type {expected_in_t}, got {actual_in_t}")

            out = spec_func(self.pargs, *args)

            if not isinstance(out, tuple):
                raise TypeError(f"{self.name} expects a tuple output value, got {type(out)}")

            assert all((isinstance(o, ss.Term) and o.get_sort().get_sort_kind() == BV) for o in out)

            actual_out_t = tuple(o.get_sort().get_width() for o in out)
            if not expected_out_t == actual_out_t:
                raise TypeError(f"{self.name} expects output values of type {expected_out_t}, got {actual_out_t}")
            
            return out

        attributes["timing"] = timing
        attributes["eval"] = tc_spec_func
        attributes["is_moores"] = is_moores
        return type(name, (self.SpecNode,), attributes)