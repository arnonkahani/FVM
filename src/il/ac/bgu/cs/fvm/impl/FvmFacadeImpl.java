package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.*;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its 
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade {

    @Override
    public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem() {
       return new TransitionSystemImpl<S,A,P>();
    }

    @Override
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        Map<S,Map<A,S>> transitions = new HashMap(); 
    		for(Transition<S,A> t: ts.getTransitions()) {
    			S from = t.getFrom();
    			S to = t.getTo();
    			A action = t.getAction();
        		if(transitions.containsKey(from))
        		{        
        			if(transitions.get(from).containsKey(action)) {
        				return false;
        			}else {
        				transitions.get(from).put(action, to);
        			}
        		}else {
        			Map<A,S> actions = new HashMap<A,S>();
        			actions.put(action, to);
        			transitions.put(from,actions);
        		}
    		}
    		return true && (ts.getInitialStates().size() <= 1);
    		
    }

    @Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
       for(S s : ts.getStates()) {
	    	   Set<S> s1 = this.pre(ts, s);
	    	   Set<P> s2 = new HashSet<P>();
	    	   for(S preState : s1) {
	    		   P p = (P) ts.getLabel(preState);
	    		   if(s2.contains(p))
	    			   return false;
	    		   else
	    			   s2.add(p);
	    	   }
       }
       return true && (ts.getInitialStates().size() <= 1);
    }

    @Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
    		return isExecutionFragment(ts,e) && isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e);
    		
    }

    @Override
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
    		AlternatingSequence ae = e;
		while(!ae.isEmpty()) {
			S s = (S) ae.head();
			if(!ts.getStates().contains(s))
				throw new StateNotFoundException(s);
			if(ae.size() == 1)
				return true;
			ae = ae.tail();
			A a = (A) ae.head();
			if(!ts.getActions().contains(a))
				throw new ActionNotFoundException(a);
			ae = ae.tail();
			Set<S> postStates = this.post(ts, s, a);
			if(!ts.getStates().contains(ae.head()))
				throw new StateNotFoundException(ae.head());
			if(!postStates.contains(ae.head()))
				return false;
			
		}
		return true;
    }

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
    		AlternatingSequence ae = e;
		return this.isExecutionFragment(ts,e) && ts.getInitialStates().contains(e.head());
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
    		return (isExecutionFragment(ts,e) && this.post(ts,e.last()).isEmpty());
    }

    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
	    	if(!ts.getStates().contains(s))
	        throw new StateNotFoundException(s);
	    	return this.post(ts, s).size() == 0;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
    		Set<S> ans = new HashSet<S>();
        for(Transition t : ts.getTransitions())
        		if(t.getFrom().equals(s))
        			ans.add((S) t.getTo());
        return ans;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
    		Set<S> ans = new HashSet<S>();    
    		for(S s: c)
    			ans.addAll(this.post(ts,s));
    		return ans;
        	
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
    		Set<S> ans = new HashSet<S>();
        for(Transition t : ts.getTransitions())
        		if(t.getFrom().equals(s) && t.getAction().equals(a))
        			ans.add((S) t.getTo());
        return ans;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
    		Set<S> ans = new HashSet<S>();    
		for(S s: c)
			ans.addAll(this.post(ts,s,a));
		return ans;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> ans = new HashSet<S>();
        for(Transition t : ts.getTransitions())
        		if(t.getTo().equals(s))
        			ans.add((S) t.getFrom());
        return ans;
        }
        
    

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
    		Set<S> ans = new HashSet<S>();    
		for(S s: c)
			ans.addAll(this.pre(ts,s));
		return ans;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
    	Set<S> ans = new HashSet<S>();
        for(Transition t : ts.getTransitions())
        		if(t.getTo().equals(s) && t.getAction().equals(a))
        			ans.add((S) t.getFrom());
        return ans;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> ans = new HashSet<S>();    
		for(S s: c)
			ans.addAll(this.pre(ts,s,a));
		return ans;
    }
    
    private <S,A> void isReachable(TransitionSystem<S, A, ?> ts,S s,Set<S> ans) {
    		if(ans.contains(s))
    			return;
    		ans.add(s);
    		for(S postS : this.post(ts,s))
    			isReachable(ts, postS, ans);
    }
    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
    	Set<S> ans = new HashSet<S>();
    	for(S s : ts.getInitialStates()) {
    		isReachable(ts,s,ans);
    	}
    	return ans;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement createProgramGraph
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromCircuit
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromProgramGraph
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromChannelSystem
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromelaString
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement verifyAnOmegaRegularProperty
    }

    @Override
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement LTL2NBA
    }

    @Override
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement GNBA2NBA
    }

   
}
