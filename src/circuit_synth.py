from src.cegis import Cegis
from src.circuit_encoding import CircuitEncoding
import functools
import pono
import smt_switch.primops as pops
from smt_switch.sortkinds import BOOL, BV

class CircuitSynth:
    def __init__(self, nodes, types, ops, spec_func, num_cycles, enforce_timing = False, input_delays = None, cycle_delay = None, max_output_delays = None):
        self.enc = CircuitEncoding(nodes, types, ops, input_delays)
        self.ur = pono.Unroller(nodes.fts)
        self.solver = nodes.fts.solver

        if enforce_timing:
            assert input_delays is not None
            assert cycle_delay is not None
            assert max_output_delays is not None

            cycle_delay = self.solver.make_term(cycle_delay, self.solver.make_sort(BV, nodes.delay_width))
            zero = self.solver.make_term(0, self.solver.make_sort(BV, nodes.delay_width))
            setup_conds = tuple(self.solver.make_term(pops.BVSle, setup, cycle_delay) for setup in self.enc.setups)
            hold_conds = tuple(self.solver.make_term(pops.BVSge, hold, zero) for hold in self.enc.holds)
            assert len(self.enc.output_delays) == len(max_output_delays)
            max_output_delays = tuple(self.solver.make_term(d, self.solver.make_sort(BV, nodes.delay_width)) for d in max_output_delays)
            assert len(self.enc.output_delays) == len(max_output_delays)
            output_delay_conds = tuple(self.solver.make_term(pops.BVSle, delay, max_delay) for delay,max_delay in zip(self.enc.output_delays, max_output_delays))
            P_timing = functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), setup_conds + hold_conds + output_delay_conds)
            synth_base = functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), [P_timing, self.enc.P_conn_delays, self.enc.P_wfp])
        else:
            synth_base = self.enc.P_wfp

        P_conn_vars = []
        for n in range(num_cycles + 1):
            P_conn_vars.append(self.ur.at_time(self.enc.P_conn_vars, n))
        P_conn_vars = functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), P_conn_vars)

        P_state = [self.ur.at_time(nodes.fts.init, 0)]
        for n in range(num_cycles):
            P_state.append(self.ur.at_time(nodes.fts.trans, n))
        P_state = functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), P_state)

        P_spec_nodes = [self.solver.make_term(1, self.solver.make_sort(BOOL))]
        for input_vars,output_vars,op in zip(self.enc.op_input_vars, self.enc.op_output_vars, self.enc.ops):
            if not isinstance(op, nodes.SpecNode):
                continue
            input_vars_up_to_cycle = []
            for n in range(num_cycles + 1):
                input_vars_at_cycle = tuple(self.ur.at_time(var, n) for var in input_vars)
                input_vars_up_to_cycle.append(input_vars_at_cycle)
                result_at_cycle = op.eval(*input_vars_up_to_cycle)
                output_vars_at_cycle = tuple(self.ur.at_time(var, n) for var in output_vars)
                equals = tuple(self.solver.make_term(pops.Equal, res, out) for res,out in zip(result_at_cycle, output_vars_at_cycle))
                P_spec_nodes.append(functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), equals))
        P_spec_nodes = functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), P_spec_nodes)

        P_spec = []
        input_vars = []
        for n in range(num_cycles + 1):
            input_vars.append(tuple(self.ur.at_time(var, n) for var in self.enc.input_vars))
            spec_outputs = spec_func(tuple(input_vars))
            circuit_outputs = tuple(self.ur.at_time(var, n) for var in self.enc.output_vars)
            outputs_equal = tuple(self.solver.make_term(pops.Equal, so, co) for so, co in zip(spec_outputs, circuit_outputs))
            P_spec.append(functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), outputs_equal))
        P_spec = functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), P_spec)

        synth_constrain = functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), [P_conn_vars, P_state, P_spec, P_spec_nodes])
        verify = self.solver.make_term(pops.Implies, functools.reduce(lambda a,b: self.solver.make_term(pops.And, a, b), [synth_base, P_conn_vars, P_state, P_spec_nodes]), P_spec)

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

