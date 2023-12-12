import functools
import pono
import smt_switch as ss
import smt_switch.primops as pops
from smt_switch.sortkinds import BOOL, BV
from src.nodes import Nodes
from src.circuit_synth import CircuitSynth

s = ss.create_btor_solver(False)
s.set_opt('produce-models', 'true')
s.set_opt('incremental', 'true')
fts = pono.FunctionalTransitionSystem(s)
n = Nodes(fts, 16)

def pipelined_adder(inputs):
    depth = 2
    BVsort = s.make_sort(BV, 4)
    if len(inputs) <= depth:
        return (s.make_term(0, BVsort),)
    else:
        res = functools.reduce(lambda a,b: s.make_term(pops.BVAdd, a, b), inputs[-1 - depth])
        return (res,)
    
def fib(inputs):
    BVsort = s.make_sort(BV, 4)
    if len(inputs) == 1:
        res =  s.make_term(0, BVsort)
    elif len(inputs) == 2:
        res = s.make_term(1, BVsort)
    else:
        res = s.make_term(pops.BVAdd, fib(inputs[:-1])[0], fib(inputs[:-2])[0])
    return (res,)
    
# ops = (n.Add(N = 4, delay = 1), n.Add(N = 4, delay = 2), n.Add(N = 4, delay = 2), 
#        n.Register(N = 4, init = 0, setup = 1, hold = 2, output_delay = 1), n.Register(N = 4, init = 0, setup = 2, hold = 1, output_delay = 1))
# cs = CircuitSynth(n, ((4,4,4,4),(4,)), ops, pipelined_adder, 10, enforce_timing = True, input_delays = (1,1,1,1), cycle_delay = 5, max_output_delays=(1,))
ops = (n.Add(N = 4, delay = 1),
       n.Register(N = 4, init = 0, setup = 2, hold = 1, output_delay = 0), n.Register(N = 4, init = 1, setup = 1, hold = 2, output_delay = 1))

def sequence_detector_func(pargs, *inputs):
    BVsort = s.make_sort(BV, pargs["N"])
    seq = pargs["sequence"]
    if len(inputs) < len(seq):
        res =  s.make_term(0, s.make_sort(BOOL))
    else:
        seq = tuple(s.make_term(e, BVsort) for e in seq)
        inputs = tuple(i[0] for i in inputs)
        match = tuple(s.make_term(pops.Equal, i, e) for i,e in zip(inputs[-len(seq):], seq))
        res = functools.reduce(lambda a,b: s.make_term(pops.And, a, b), match)
    return (res,)

def sequence_detector_spec(inputs):
    BVsort = s.make_sort(BV, 4)
    delay = 2
    seq = (0,2,3)
    if len(inputs) < (len(seq) + delay):
        res =  s.make_term(0, s.make_sort(BOOL))
    else:
        seq = tuple(s.make_term(e, BVsort) for e in seq)
        inputs = tuple(i[0] for i in inputs)
        if delay == 0:
            end = None
        else:
            end = -delay
        match = tuple(s.make_term(pops.Equal, i, e) for i,e in zip(inputs[-len(seq)-delay:end], seq))
        res = functools.reduce(lambda a,b: s.make_term(pops.And, a, b), match)
    return (res,)


def sequence_detector_delay_func(pargs, delay):
    delaysort = s.make_sort(BV, n.delay_width)
    setup = s.make_term(pargs["setup"], delaysort)
    delay_with_setup = s.make_term(pops.BVAdd, delay, setup)
    hold = s.make_term(pargs["hold"], delaysort)
    delay_without_hold = s.make_term(pops.BVAdd, delay, s.make_term(pops.BVNeg, hold))
    in_out_delay = s.make_term(pargs["delay"], delaysort)
    return (delay_with_setup,), (delay_without_hold,),(s.make_term(pops.BVAdd, delay, in_out_delay),)

sequence_detector_type_func = lambda pargs: ((pargs["N"],), (1,))

SequenceDetector = n.make_spec("SequenceDetector", {"N": int, "sequence": tuple, "setup": int, "hold": int, "delay": int}, sequence_detector_func, sequence_detector_type_func, sequence_detector_delay_func, (False,))

ops = (
    SequenceDetector(N = 4, sequence = (0,2,3), setup = 1, hold = 1, delay = 2),
    n.Register(N = 4, init = 0, setup = 2, hold = 1, output_delay = 1), 
    n.Register(N = 1, init = 0, setup = 1, hold = 1, output_delay = 1),
    n.Register(N = 1, init = 0, setup = 1, hold = 1, output_delay = 0),
    )
cs = CircuitSynth(n, ((4,),(1,)), ops, sequence_detector_spec, 10, enforce_timing=True, input_delays=(1,), cycle_delay=6, max_output_delays=(3,))
res = cs.run()
print(res)

