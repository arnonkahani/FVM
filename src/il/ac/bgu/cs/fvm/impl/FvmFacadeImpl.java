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
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
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
import java.util.Stack;

import com.sun.prism.impl.shape.ShapeUtil;

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
    		if(!ts.getStates().contains(s))
			throw new StateNotFoundException(s);
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
    		if(!ts.getActions().contains(a))
			throw new ActionNotFoundException(a);
    		Set<S> ans = new HashSet<S>();    
		for(S s: c)
			ans.addAll(this.post(ts,s,a));
		return ans;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
    		if(!ts.getStates().contains(s))
    			throw new StateNotFoundException(s);
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
    		if(!ts.getActions().contains(a))
    			throw new ActionNotFoundException(a);
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


    private <S1,S2,A,P> Set<Transition<Pair<S1,S2>,A>> interleaveTransitions(Set<Pair<S1,S2>> states,Set<Pair<S1,S2>> initalStates,TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions){
    	
    	Set<Pair<S1,S2>> interlivedStates = new HashSet<Pair<S1,S2>>();
    	Stack<Pair<S1,S2>> shouldTraverse = new Stack<Pair<S1,S2>>();
    	Set<Transition<S1,A>> tr1 = ts1.getTransitions();
    	Set<Transition<S2,A>> tr2 = ts2.getTransitions();
    	Set<Transition<Pair<S1,S2>,A>> interlivedTransitions = new HashSet<Transition<Pair<S1,S2>,A>>();
    	
    	for(Pair<S1,S2> initState : initalStates)
    		shouldTraverse.push(initState);
    	
    	while(!shouldTraverse.isEmpty()) {
    		Pair<S1,S2> currentState = shouldTraverse.pop();
    		interlivedStates.add(currentState);
    		//S1
    		for(Transition<S1,A> transition : tr1) {
    			if(transition.getFrom().equals(currentState.getFirst())) {
    				if (handShakingActions.contains(transition.getAction()))
                    {
                        for (Transition<S2, A> transition2 : tr2)
                        {
                            if (transition2.getAction().equals(transition.getAction()) 
                            		&& transition2.getFrom().equals(currentState.getSecond()))
                            {
                            	 	Pair<S1, S2> to = new Pair<S1,S2>(transition.getTo(),transition2.getTo());
                            	 	interlivedTransitions.add(new Transition<Pair<S1,S2>,A>(currentState, transition.getAction(), to));
                            	 	if(!interlivedStates.contains(to)) {
            							interlivedStates.add(to);
            							shouldTraverse.push(to);
            						}
                                
                            }
                        }
                    }else {
                    	Pair<S1, S2> to = new Pair<S1,S2>(transition.getTo(), currentState.getSecond());
    						if(!interlivedStates.contains(to)) {
    							interlivedStates.add(to);
    							shouldTraverse.push(to);
    							
    						}
    						interlivedTransitions.add(new Transition<Pair<S1,S2>, A>(currentState, transition.getAction(), to));
    			}
    						
    			}
    		}
    		//S2
    		for(Transition<S2,A> transition : tr2) {
    			if(transition.getFrom().equals(currentState.getSecond()) && !handShakingActions.contains(transition.getAction())) {
    				Pair<S1, S2> to = new Pair<S1,S2>(currentState.getFirst(),transition.getTo());
    						if(!interlivedStates.contains(to)) {
    							interlivedStates.add(to);
    							shouldTraverse.push(to);
    						}
    						interlivedTransitions.add(new Transition<Pair<S1,S2>, A>(currentState, transition.getAction(), to));
    			
    			}
    						
    					
    		}
    	}
    	
    	states.addAll(interlivedStates);
    return interlivedTransitions;
    }
    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
    	TransitionSystemImpl<Pair<S1, S2>, A, P> ans = new TransitionSystemImpl<Pair<S1, S2>, A, P>();
    	ans.addAllActions(ts1.getActions());
    	ans.addAllActions(ts2.getActions());
    	for(S1 s1 : ts1.getInitialStates())
    		for(S2 s2 : ts2.getInitialStates()) {
    			ans.addState(new Pair<S1,S2>(s1,s2));
    			ans.addInitialState(new Pair<S1,S2>(s1,s2));
    		}
    	
    	ans.addAllAtomicPropositions(ts1.getAtomicPropositions());
    	ans.addAllAtomicPropositions(ts2.getAtomicPropositions());
    	
    	Set<Pair<S1,S2>> statesToBeAdded = new HashSet<Pair<S1,S2>>();
    	Set<Transition<Pair<S1,S2>,A>> interleavedTransitions = interleaveTransitions(statesToBeAdded,ans.getInitialStates(), ts1, ts2, new HashSet<A>());
    	for(Pair<S1,S2> s : statesToBeAdded)
    		ans.addState(s);
    	for(Transition<Pair<S1,S2>,A> t : interleavedTransitions)
    		ans.addTransition(t);
    	for(Pair<S1,S2> statePair : ans.getStates()) {
    		Set<P> firstLabels = ts1.getLabel(statePair.first);
    		for(P firstLabel : firstLabels) {
    			ans.addToLabel(statePair, firstLabel);
    		}
    		Set<P> secondLabels = ts2.getLabel(statePair.second);
    		for(P secondLabel : secondLabels) {
    			ans.addToLabel(statePair, secondLabel);
    		}
    	}
    	
    	
    	
    			
    	return ans;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
    	TransitionSystem<Pair<S1, S2>, A, P> ts = interleave(ts1, ts2);
    	ts.getStates().clear();
    	Set<Pair<S1,S2>> statesToBeAdded = new HashSet<Pair<S1,S2>>();
    	Set<Transition<Pair<S1,S2>,A>> interleavedTransitions = interleaveTransitions(statesToBeAdded,ts.getInitialStates(), ts1, ts2, handShakingActions);
    	ts.getTransitions().clear();
    	for(Pair<S1,S2> s : statesToBeAdded)
    		ts.addState(s);
    	for(Transition<Pair<S1,S2>,A> t : interleavedTransitions)
    		ts.addTransition(t);
    	
    	return ts;
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
    		return new ProgramGraphImpl<L, A>();
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
    		ProgramGraph<Pair<L1, L2>, A> pg = createProgramGraph();

        for (L1 loc1 : pg1.getLocations())
            for (L2 loc2 : pg2.getLocations())
            {
                Pair<L1, L2> location = new Pair<L1,L2>(loc1, loc2);
                pg.addLocation(location);
            }

        for (L1 initLoc1 : pg1.getInitialLocations())
            for (L2 initLoc2 : pg2.getInitialLocations())
            {
                Pair<L1, L2> location = new Pair<L1,L2>(initLoc1, initLoc2);
                pg.addInitialLocation(location);
            }

        for (List<String> initalization1 : pg1.getInitalizations())
            for (List<String> initalization2 : pg2.getInitalizations())
            {
                List<String> initalization = new ArrayList<>();
                initalization.addAll(initalization1);
                initalization.addAll(initalization2);
                pg.addInitalization(initalization);
            }


        Set<Pair<L1, L2>> locations = pg.getLocations();

        //add transitions
        for (PGTransition<L1, A> t1 : pg1.getTransitions())
            for (Pair<L1, L2> from : locations)
                if (from.getFirst().equals(t1.getFrom()))
                {
                		Pair<L1, L2> to = null;
                		for (Pair<L1, L2> location : locations)
                        if (location.first.equals(t1.getTo()) && location.second.equals(from.second))
                        		to = location;
                    PGTransition<Pair<L1, L2>, A> transition = new PGTransition<Pair<L1, L2>, A>(from, t1.getCondition(), t1.getAction(), to);
                    pg.addTransition(transition);
                }

        for (PGTransition<L2, A> t2 : pg2.getTransitions())
            for (Pair<L1, L2> from : locations)
                if (from.second.equals(t2.getFrom()))
                {
                    Pair<L1, L2> to = null;
                    for (Pair<L1, L2> location : locations)
                        if (location.second.equals(t2.getTo()) && location.first.equals(from.first))
                        		to = location;
                    PGTransition<Pair<L1, L2>, A> transition = new PGTransition<Pair<L1, L2>, A>(from, t2.getCondition(), t2.getAction(), to);
                    pg.addTransition(transition);
                }


        return pg;
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromCircuit
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
    	TransitionSystem<Pair<L, Map<String, Object>>, A, String> ret = createTransitionSystem();
        Set<PGTransition<L, A>> transitions = pg.getTransitions();
        Set<List<String>> initializations = pg.getInitalizations();

        Set<L> initialLocations = pg.getInitialLocations();
        Stack<Pair<L, Map<String, Object>>> reach = new Stack<>();

        for (L initLoc : initialLocations)
		{
			boolean flag = true;
			for (List<String> conditions : initializations)
			{
				flag = false;
				Map<String, Object> initial_eval = new HashMap<>();
				for (String cond : conditions)
				{
					initial_eval = ActionDef.effect(actionDefs, initial_eval, cond);

				}
				Pair<L, Map<String, Object>> state = new Pair<L, Map<String, Object>>(initLoc, initial_eval);
				ret.addState(state);
				ret.addInitialState(state);
				reach.add(state);

				labelState(ret, state);
			}

			if(flag)
			{
				Map<String, Object> initial_eval = new HashMap<>();
				Pair<L, Map<String, Object>> state = new Pair<L, Map<String, Object>>(initLoc, initial_eval);
				ret.addState(state);
				ret.addInitialState(state);
				reach.add(state);
				labelState(ret, state);
			}

		}

        while (!reach.isEmpty())
        {
            Pair<L, Map<String, Object>> from = reach.poll();
            for (PGTransition<L, A> transition : transitions)
            {
                if (transition.getFrom().equals(from.first) && ConditionDef.evaluate(conditionDefs, from.second, transition.getCondition()))
                {
                    //  ret.addAtomicProposition(transition.getCondition());
                    ret.addAction(transition.getAction());
                    Pair<L, Map<String, Object>> to = new Pair<L, Map<String, Object>>(transition.getTo(), ActionDef.effect(actionDefs, from.second, transition.getAction()));
                    if (!ret.getStates().contains(to))
                    {
                        ret.addState(to);
                        reach.add(to);
                    }
                    ret.addTransition(new Transition<Pair<L, Map<String, Object>>, A>(from, transition.getAction(), to));

                    labelState(ret, to);
                }
            }
        }


        return ret;
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
//
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
