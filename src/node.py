import hwtypes as ht

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

def make_comb(name, params, eval_func, type_func):
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
        
        self.type = type_func(pargs)
        self.name = name
    
    def to_string(self):
        s = ",".join(f"{k}={self.pargs[k]}" for k in params.keys())
        return f"{name}<{s}>"
    
    def tc_eval_func(self, *args):
        assert all(isinstance(a, ht.SMTBitVector) or isinstance(a, ht.SMTBit) for a in args)
        expected_in_t = self.type[0]
        expected_out_t = self.type[1]
        actual_in_t = tuple(a.num_bits if isinstance(a, ht.SMTBitVector) else None for a in args)
        if not expected_in_t == actual_in_t:
            raise TypeError(f"{self.name} expects input values of type {expected_in_t}, got {actual_in_t}")

        out = eval_func(*args)
        if not isinstance(out, tuple):
            raise TypeError(f"{self.name} expects a tuple output value, got {type(out)}")

        assert all(isinstance(o, ht.SMTBitVector) or isinstance(o, ht.SMTBit) for o in out)

        actual_out_t = tuple(o.num_bits if isinstance(o, ht.SMTBitVector) else None for o in out)
        if not expected_out_t == actual_out_t:
            raise TypeError(f"{self.name} expects output values of type {expected_out_t}, got {actual_out_t}")
        
        return out


    attributes = {
        "__init__": init,
        "__str__": to_string,
        "eval": tc_eval_func
    }

    return type(name, (CombNode,), attributes)


Add = make_comb("Add", {"N": int}, lambda x, y: (x + y,), lambda pargs: ((pargs["N"], pargs["N"]), (pargs["N"],)))
Sub = make_comb("Sub", {"N": int}, lambda x, y: (x - y,), lambda pargs: ((pargs["N"], pargs["N"]), (pargs["N"],)))
Mul = make_comb("Mul", {"N": int}, lambda x, y: (x * y,), lambda pargs: ((pargs["N"], pargs["N"]), (pargs["N"],)))

And = make_comb("And", {"N": int}, lambda x, y: (x & y,), lambda pargs: ((pargs["N"], pargs["N"]), (pargs["N"],)))
Or = make_comb("Or", {"N": int}, lambda x, y: (x | y,), lambda pargs: ((pargs["N"], pargs["N"]), (pargs["N"],)))
Xor = make_comb("Xor", {"N": int}, lambda x, y: (x ^ y,), lambda pargs: ((pargs["N"], pargs["N"]), (pargs["N"],)))

Equals = make_comb("Equals", {"N": int}, lambda x, y: (x == y,), lambda pargs: ((pargs["N"], pargs["N"]), (None,)))
Lt = make_comb("Lt", {"N": int}, lambda x, y: (x < y,), lambda pargs: ((pargs["N"], pargs["N"]), (None,)))
Gt = make_comb("Gt", {"N": int}, lambda x, y: (x > y,), lambda pargs: ((pargs["N"], pargs["N"]), (None,)))
Lte = make_comb("Lte", {"N": int}, lambda x, y: (x <= y,), lambda pargs: ((pargs["N"], pargs["N"]), (None,)))
Gte = make_comb("Gte", {"N": int}, lambda x, y: (x >= y,), lambda pargs: ((pargs["N"], pargs["N"]), (None,)))

Mux = make_comb("Mux", {"N": int}, lambda s, x, y: (s.ite(x, y),), lambda pargs: ((None, pargs["N"], pargs["N"]), (pargs["N"],)))