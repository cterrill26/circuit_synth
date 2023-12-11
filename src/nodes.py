import pono
import smt_switch as ss
import smt_switch.primops as ops
from smt_switch.sortkinds import BV


class Nodes:
    def __init__(self, fts):
        self.fts = fts
        solver = fts.solver

        self.Add = self.make_comb("Add", {"N": int}, lambda x, y: (solver.make_term(ops.BVAdd, x, y),), lambda pargs: ((pargs["N"], pargs["N"]), (pargs["N"],)))
        self.Sub = self.make_comb("Sub", {"N": int}, lambda x, y: (solver.make_term(ops.BVSub, x, y),), lambda pargs: ((pargs["N"], pargs["N"]), (pargs["N"],)))
        self.Mul = self.make_comb("Mul", {"N": int}, lambda x, y: (solver.make_term(ops.BVMul, x, y),), lambda pargs: ((pargs["N"], pargs["N"]), (pargs["N"],)))

        self.And = self.make_comb("And", {"N": int}, lambda x, y: (solver.make_term(ops.BVAnd, x, y),), lambda pargs: ((pargs["N"], pargs["N"]), (pargs["N"],)))
        self.Or = self.make_comb("Or", {"N": int}, lambda x, y: (solver.make_term(ops.BVOr, x, y),), lambda pargs: ((pargs["N"], pargs["N"]), (pargs["N"],)))
        self.Xor = self.make_comb("Xor", {"N": int}, lambda x, y: (solver.make_term(ops.BVXor, x, y),), lambda pargs: ((pargs["N"], pargs["N"]), (pargs["N"],)))

        self.Equal = self.make_comb("Equals", {"N": int}, lambda x, y: (solver.make_term(ops.Equal, x, y),), lambda pargs: ((pargs["N"], pargs["N"]), (1,)))
        self.Ult = self.make_comb("Lt", {"N": int}, lambda x, y: (solver.make_term(ops.BVUlt, x, y),), lambda pargs: ((pargs["N"], pargs["N"]), (1,)))
        self.Ugt = self.make_comb("Gt", {"N": int}, lambda x, y: (solver.make_term(ops.BVUgt, x, y),), lambda pargs: ((pargs["N"], pargs["N"]), (1,)))
        self.Ule = self.make_comb("Lte", {"N": int}, lambda x, y: (solver.make_term(ops.BVUle, x, y),), lambda pargs: ((pargs["N"], pargs["N"]), (1,)))
        self.Uge = self.make_comb("Gte", {"N": int}, lambda x, y: (solver.make_term(ops.BVUge, x, y),), lambda pargs: ((pargs["N"], pargs["N"]), (1,)))

        self.Mux = self.make_comb("Mux", {"N": int}, lambda s, x, y: (solver.make_term(ops.Ite, s, x, y),), lambda pargs: ((1, pargs["N"], pargs["N"]), (pargs["N"],)))

        def register_eval_func(inst, d):
            BVN = solver.make_sort(BV, inst.pargs["N"])

            reg = fts.make_statevar(f"Register{type(inst).count}", BVN)
            type(inst).count += 1

            fts.constrain_init(solver.make_term(ops.Equal, reg, solver.make_term(inst.pargs["init"], BVN)))
            fts.assign_next(reg, d)
            return (reg,),(reg,)

        self.Register = self.make_seq("Register", {"N": int, "init": int}, register_eval_func, lambda pargs: ((pargs["N"],), (pargs["N"],)))


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
    

    def make_seq(self, name, params, eval_func, type_func):
        attributes = self.make_attributes(name, params, eval_func, True, type_func)
        attributes["count"] = 0
        return type(name, (self.SeqNode,), attributes)


    def make_comb(self, name, params, eval_func, type_func):
        attributes = self.make_attributes(name, params, eval_func, False, type_func)
        return type(name, (self.CombNode,), attributes)
