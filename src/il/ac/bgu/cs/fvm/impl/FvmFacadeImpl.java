package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.channelsystem.InterleavingActDef;
import il.ac.bgu.cs.fvm.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.*;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.OptionContext;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;
import java.util.stream.IntStream;
import static java.util.stream.Collectors.toList;

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
    		Set<P> firstLabels = ts1.getLabel(statePair.getFirst());
    		for(P firstLabel : firstLabels) {
    			ans.addToLabel(statePair, firstLabel);
    		}
    		Set<P> secondLabels = ts2.getLabel(statePair.getSecond());
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

        for (PGTransition<L1, A> t1 : pg1.getTransitions())
            for (Pair<L1, L2> from : locations)
                if (from.getFirst().equals(t1.getFrom()))
                {
                		Pair<L1, L2> to = null;
                		for (Pair<L1, L2> location : locations)
                        if (location.getFirst().equals(t1.getTo()) && location.getSecond().equals(from.getSecond()))
                        		to = location;
                    PGTransition<Pair<L1, L2>, A> transition = new PGTransition<Pair<L1, L2>, A>(from, t1.getCondition(), t1.getAction(), to);
                    pg.addTransition(transition);
                }

        for (PGTransition<L2, A> t2 : pg2.getTransitions())
            for (Pair<L1, L2> from : locations)
                if (from.getSecond().equals(t2.getFrom()))
                {
                    Pair<L1, L2> to = null;
                    for (Pair<L1, L2> location : locations)
                        if (location.getSecond().equals(t2.getTo()) && location.getFirst().equals(from.getFirst()))
                        		to = location;
                    PGTransition<Pair<L1, L2>, A> transition = new PGTransition<Pair<L1, L2>, A>(from, t2.getCondition(), t2.getAction(), to);
                    pg.addTransition(transition);
                }


        return pg;
    }
    
    private void permutations(Set<boolean[]> perms,boolean[] perm,int index){
    		if(index != perm.length) {
	    		perms.add(perm.clone());
	    		int newIndex = index + 1;
	    		permutations(perms,perm.clone(),newIndex);
	    		perm[index] = true;
	    		perms.add(perm.clone());
	    		permutations(perms,perm.clone(),newIndex);
    		}
    }
    
    
    private Set<boolean[]> permutations(int numberOfInputs){
    		Set<boolean[]> perms = new HashSet<boolean []>();
    		 permutations(perms,new boolean[numberOfInputs],0);
    		 return perms;
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object>  transitionSystemFromCircuit(Circuit c) {
    		TransitionSystem<Pair<Map<String,Boolean>, Map<String,Boolean>>, Map<String, Boolean>, Object> ts = createTransitionSystem();
        Set<String> registersNames = c.getRegisterNames();
        Set<String> inputsNames = c.getInputPortNames();
        Set<String> outputsNames = c.getOutputPortNames();
        Set<boolean[]> inputValues = permutations(inputsNames.size());


        String[] inputesNamesArray = new String[inputsNames.size()];
        inputsNames.toArray(inputesNamesArray);
        for (boolean[] perm : inputValues)
        {
        		Map<String, Boolean> action = new HashMap<String, Boolean>();
            for(int i=0;i<inputesNamesArray.length;i++) {
            		action.put(inputesNamesArray[i], perm[i]);
            }
            ts.addAction(action);
            		
        }

        for (String s : registersNames)
            ts.addAtomicProposition(s);
        for (String s : inputsNames)
            ts.addAtomicProposition(s);
        for (String s : outputsNames)
            ts.addAtomicProposition(s);



      

        for (Map<String,Boolean> action : ts.getActions())
        {
        		Map<String, Boolean> initRegisters = new HashMap<String, Boolean>();
            for(String s : registersNames) {
            	initRegisters.put(s,false);
            }
            Pair<Map<String, Boolean>, Map<String, Boolean>> state = new Pair<Map<String, Boolean>, Map<String, Boolean>>(action,initRegisters);
            ts.addState(state);
            ts.addInitialState(state); 
        }
        
//        Set<boolean[]> registerValues = permutations(inputsNames.size());
//        int rv_s = registerValues.size();
//        registerValues.removeIf(x -> {for(boolean b : x) if(b == true) return false; return true;});
//        String[] registersNamesArray = new String[registersNames.size()];
//        registersNames.toArray(registersNamesArray);
//        for (boolean[] perm : registerValues)
//        {
//        		Map<String, Boolean> reg = new HashMap<String, Boolean>();
//            for(int i=0;i<registersNamesArray.length;i++) {
//            		reg.put(registersNamesArray[i], perm[i]);
//            }
//            for(Map<String,Boolean> action : ts.getActions()) {
//            	Pair<Map<String, Boolean>, Map<String, Boolean>> state = new Pair<Map<String, Boolean>, Map<String, Boolean>>(action,reg);
//            	ts.addState(state);
//            }
//            
//        }
        
      
        
        
      	Stack<Pair<Map<String, Boolean>, Map<String, Boolean>>> reachabelStates = new Stack<Pair<Map<String, Boolean>, Map<String, Boolean>>>();
      	for(Pair<Map<String, Boolean>, Map<String, Boolean>> initalState : ts.getInitialStates())
      		reachabelStates.push(initalState);
      	Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> checkedStates = new HashSet<Pair<Map<String, Boolean>, Map<String, Boolean>>>();
        while (!reachabelStates.isEmpty())
        {
        	
            Pair<Map<String, Boolean>, Map<String, Boolean>> from = reachabelStates.pop();
            checkedStates.add(from);
            for (Map<String, Boolean> action : ts.getActions())
            {
                Map<String, Boolean> updatedRegs = c.updateRegisters(from.first, from.second);
                Pair<Map<String, Boolean>, Map<String, Boolean>> to = new Pair<Map<String, Boolean>, Map<String, Boolean>>(action,updatedRegs);
                if (!checkedStates.contains(to))
                {
                		ts.addState(to);
                    reachabelStates.push(to);
                }
                ts.addTransition(new Transition<>(from, action, to));
            }
        }
       
        
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : ts.getStates())
        {
      	  	
      	  	for(Entry<String, Boolean> output : state.first.entrySet())
          	 	if(output.getValue())
          	 		ts.addToLabel(state, output.getKey());
      	  	for(Entry<String, Boolean> output : state.second.entrySet())
          	 	if(output.getValue())
          	 		ts.addToLabel(state, output.getKey());
           Map<String, Boolean> outputs = c.computeOutputs(state.first, state.second);
           for(Entry<String, Boolean> output : outputs.entrySet())
          	 	if(output.getValue())
          	 		ts.addToLabel(state, output.getKey());
        }

        return ts;
    }
    
    private <L, A> void labelStateInTS(TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts, Pair<L, Map<String, Object>> state)
    {
        ts.addAtomicProposition(state.first.toString());
        ts.addToLabel(state, state.first.toString());
        for (Map.Entry<String, Object> entry : state.second.entrySet())
        {
            String ap = entry.getKey().toString() + " = " + entry.getValue().toString();
            ts.addAtomicProposition(ap);
            ts.addToLabel(state, ap);
        }
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
				reach.push(state);

				labelStateInTS(ret, state);
			}

			if(flag)
			{
				Map<String, Object> initial_eval = new HashMap<>();
				Pair<L, Map<String, Object>> state = new Pair<L, Map<String, Object>>(initLoc, initial_eval);
				ret.addState(state);
				ret.addInitialState(state);
				reach.push(state);
				labelStateInTS(ret, state);
			}

		}

        while (!reach.isEmpty())
        {
            Pair<L, Map<String, Object>> from = reach.pop();
            for (PGTransition<L, A> transition : transitions)
            {
                if (transition.getFrom().equals(from.getFirst()) && ConditionDef.evaluate(conditionDefs, from.getSecond(), transition.getCondition()))
                {
                    ret.addAction(transition.getAction());
                    Pair<L, Map<String, Object>> to = new Pair<L, Map<String, Object>>(transition.getTo(), ActionDef.effect(actionDefs, from.getSecond(), transition.getAction()));
                    if (!ret.getStates().contains(to))
                    {
                        ret.addState(to);
                        reach.push(to);
                    }
                    ret.addTransition(new Transition<Pair<L, Map<String, Object>>, A>(from, transition.getAction(), to));
                    labelStateInTS(ret, to);
                }
            }
        }
        return ret;
    }
    
    public static <E> List<E> generateFlatPerm(List<Set<E>> original)
    {
        List<Set<E>> copy = new ArrayList<Set<E>>(original);
        List<List<E>> copyPerm = generatePerm(copy);
        List<E> flat = flat_list(copyPerm);
        return flat;
    }

    public static <E> List<E> flat_list(List<List<E>> flat)
    {
        List<E> ret = new ArrayList<E>();
        for (List<E> list : flat)
            ret.addAll(list);
        return ret;
    }

    public static <E> List<List<E>> generatePerm(List<Set<E>> original)
    {
        if (original.size() == 0)
        {
            List<List<E>> result = new ArrayList<List<E>>();
            result.add(new ArrayList<E>());
            return result;
        }
        Set<E> firstElement = original.remove(0);
        List<List<E>> returnValue = new ArrayList<List<E>>();
        List<List<E>> permutations = generatePerm(original);
        for (List<E> smallerPermutated : permutations)
        {
            if(firstElement.size() == 0)
            {
                returnValue.add(smallerPermutated);
            }
            else
            {
                for (E element : firstElement)
                {
                    List<E> temp = new ArrayList<E>(smallerPermutated);
                    temp.add(0, element);
                    returnValue.add(temp);
                }
            }
        }
        return returnValue;
    }
    private <L, A> void labelComplexState(TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts, Pair<List<L>, Map<String, Object>> state)
    {
        for(L location : state.first)
        {
            ts.addAtomicProposition(location.toString());
            ts.addToLabel(state, location.toString());
        }
        for (Map.Entry<String, Object> entry : state.second.entrySet())
        {
            String ap = entry.getKey().toString() + " = " + entry.getValue().toString();
            ts.addAtomicProposition(ap);
            ts.addToLabel(state, ap);
        }
    }
    
    private <L, A> void handleTransition(TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ret, Set<ActionDef> actionDefs, Stack<Pair<List<L>, Map<String, Object>>> reach, Pair<List<L>, Map<String, Object>> state, A action, List<L> new_location)
    {
        Map<String, Object> newEval = ActionDef.effect(actionDefs, state.second, action);
        if (newEval != null )
        {
            Pair<List<L>, Map<String, Object>> newState = new Pair<>(new_location, newEval);
            Transition<Pair<List<L>, Map<String, Object>>, A> transition = new Transition<>(state, action, newState);
            if (!ret.getStates().contains(newState))
            {
                reach.push(newState);
                ret.addState(newState);
            }
            ret.addAction(action);
            ret.addTransition(transition);
            labelComplexState(ret, newState);
        }
    }

    private <L, A> Pair<List<L>, Map<String, Object>> create_state(TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ret, Set<ActionDef> actionDefs, Pair<List<L>, Map<String, Object>> state, A action, List<L> new_location)
    {

        Map<String, Object> eval = ActionDef.effect(actionDefs, state.second, action);
        if (eval != null)
        {
            return new Pair<>(new_location, eval);
        }
        return null;
    }

    private <L> Set<Pair<List<L>, Map<String, Object>>> generate_initial_states(List<List<L>> initial_locations_permutations, Set<Map<String, Object>> initials_actions)
    {
        Set<Pair<List<L>, Map<String, Object>>> ret = new HashSet<>();
        for (List<L> location : initial_locations_permutations)
            for (Map<String, Object> initial_action : initials_actions)
                ret.add(new Pair(location, initial_action));
        return ret;
    }

    private static Set<Map<String, Object>> generate_initial_actions(List<List<String>> initializations, Set<ActionDef> actionDefs)
    {
        Set<Map<String, Object>> ret = new HashSet<>();
        for (List<String> initialization : initializations)
        {
            Map<String, Object> eval = new HashMap<>();
            for (String action : initialization)
            {
                eval = ActionDef.effect(actionDefs, eval, action);
            }
            ret.add(eval);
        }
        if (ret.size() == 0)
        {
            ret.add(new HashMap<>());
        }
        return ret;
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
			ChannelSystem<L, A> cs) {
    	TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ret = createTransitionSystem();
        List<ProgramGraph<L, A>> programGraphs = cs.getProgramGraphs();

        //combine all initializations
        List<Set<List<String>>> initializations = new ArrayList<Set<List<String>>>();
        for (ProgramGraph<L, A> pg : programGraphs)
        {
            initializations.add(pg.getInitalizations());

        }

        //combine all initial locations
        List<Set<L>> initialLocations = new ArrayList<Set<L>>();
        for (ProgramGraph<L, A> pg : programGraphs)
        {
        	initialLocations.add(pg.getInitialLocations());
        }

        List<List<String>> initializationsPermutations = generateFlatPerm(initializations);

        // Normal parser for normal operation and unlimited channel.
        Set<ActionDef> actionDefs = new HashSet<>();
        InterleavingActDef actionDef = new ParserBasedInterleavingActDef();
        actionDefs.add(actionDef);
        actionDefs.add(new ParserBasedActDef());

        // for zero capacity channel.
        Set<ActionDef> complexActionDefSet = new HashSet<>();
        complexActionDefSet.add(new ParserBasedInterleavingActDef());

        // for conditions
        ConditionDef conditionDef = new ParserBasedCondDef();
        Set<ConditionDef> conditionDefs = new HashSet<>();
        conditionDefs.add(conditionDef);


        Set<Map<String, Object>> initials_actions = generate_initial_actions(initializationsPermutations, actionDefs);

        List<List<L>> initial_locations_permutations = generatePerm(initialLocations);

        Set<Pair<List<L>, Map<String, Object>>> initials_states = generate_initial_states(initial_locations_permutations, initials_actions);
        Stack<Pair<List<L>, Map<String, Object>>> reach = new Stack<Pair<List<L>, Map<String, Object>>>();

        //add all states as initial states and add atomic propositions.
        for (Pair<List<L>, Map<String, Object>> state : initials_states)
        {
            ret.addState(state);
            ret.addInitialState(state);
            reach.push(state);

            labelComplexState(ret, state);

        }

        while (!reach.isEmpty())
        {
            Pair<List<L>, Map<String, Object>> from = reach.pop();
            Map<Integer, List<PGTransition<L, A>>> simultaneous_actions = new HashMap<>();
            for (int i = 0; i < programGraphs.size(); i++)
            {
                ProgramGraph<L, A> current_pg = programGraphs.get(i);
                L current_location = from.getFirst().get(i);
                //iterate over all transitions to find those who are from "from" location and all the conditions are passed.
                for (PGTransition<L, A> pgTransition : current_pg.getTransitions())
                {
                    if (pgTransition.getFrom().equals(current_location)
                            && ConditionDef.evaluate(conditionDefs, from.second, pgTransition.getCondition()))
                    {
                        //we need to check if the action is one-sided or not
                        A action = pgTransition.getAction();
                        if (!actionDef.isOneSidedAction(action.toString()))
                        {
                            // create new location when the i-location is changed.
                            List<L> new_location = new ArrayList<>(from.first);
                            new_location.set(i, pgTransition.getTo());
                            handleTransition(ret, actionDefs, reach, from, action, new_location);
                        } else
                        {
                            if (!simultaneous_actions.containsKey(i))
                            {
                                simultaneous_actions.put(i, new ArrayList<>());
                            }
                            simultaneous_actions.get(i).add(pgTransition);
                        }
                    }
                }
                if (simultaneous_actions.size() > 0)
                {
                    // build list of all possible operation in order to calc permutation.
                    List<Set<Pair<Integer, PGTransition<L, A>>>> allComplexTransitions = new ArrayList<>();
                    for (Integer key : simultaneous_actions.keySet())
                    {
                        List<PGTransition<L, A>> transitions = simultaneous_actions.get(key);
                        Set<Pair<Integer, PGTransition<L, A>>> set = new HashSet<>();
                        for (PGTransition<L, A> transition : transitions)
                        {
                            set.add(new Pair<>(key, transition));
                        }
                        allComplexTransitions.add(set);
                    }
                    // compute permutation.
                    List<List<Pair<Integer, PGTransition<L, A>>>> allComplexTransitionPermutations = generatePerm(allComplexTransitions);
                    // for each permutation, we will check all the possible executions.
                    for (List<Pair<Integer, PGTransition<L, A>>> complexTransition : allComplexTransitionPermutations)
                    {
                        // handle the complex operation by creating merging them:
                        StringBuilder action = new StringBuilder();
                        List<L> newLocation = new ArrayList<>(from.first);
                        List<A> actions = new ArrayList<>();
                        for (Pair<Integer, PGTransition<L, A>> pair : complexTransition)
                        {
                            if (action.length() != 0)
                            {
                                action.append("|");
                            }
                            action.append(pair.second.getAction());
                            actions.add(pair.second.getAction());
                            newLocation.set(pair.first, pair.second.getTo());
                        }
                        // we have the newLocation and a join action,
                        // we will handle the transition
                        if (!actionDef.isOneSidedAction(actions.toString()) && complexTransition.size() > 1)
                        {
                            handleTransition(ret, complexActionDefSet, reach, from, (A) action.toString(), newLocation);
                        }
                    }
                }
            }
        }

        return ret;
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
    		StmtContext root= NanoPromelaFileReader.pareseNanoPromelaFile(filename);

		ProgramGraph<String, String> pg = pgFromRoot(root);

		return pg;
    }
    
private ProgramGraph<String, String> pgFromRoot(StmtContext root) {
		
		ProgramGraph<String, String> pg = createProgramGraph();
		
		HashSet<String> loc = new HashSet<String>();
		loc = sub(root , loc , pg);
		
		for(String  locToAdd : loc){
			pg.addLocation(locToAdd);
		}

		pg.addInitialLocation(root.getText());
		HashSet<String> reachableLocs = reachableOnly(pg);
		
		String[] locToRemove = new String[pg.getLocations().size()];
		pg.getLocations().toArray(locToRemove);
			
		int length = locToRemove.length;
		
		for(int i=0;i<length;i++)
			pg.removeLocation(locToRemove[i]);
		
		for(String  locToAdd : reachableLocs){
			pg.addLocation(locToAdd);
		}
		pg.addInitialLocation(root.getText());
		
		removeWasteTrans(pg);
		
		return pg;

	}

	private void removeWasteTrans(ProgramGraph<String, String> pg) {
		Set<PGTransition<String, String>> transitions = pg.getTransitions();
		Set<String> locations = pg.getLocations();
		
		for(PGTransition<String, String> trans : transitions){
			if(locations.contains(trans.getFrom()) && locations.contains(trans.getTo())){
				
			}
			else{
				pg.removeTransition(trans);
			}
		}
		
	}

	private HashSet<String> reachableOnly(ProgramGraph<String, String> pg) {
		Set<String> initialLocs = pg.getInitialLocations();
		
		HashSet<String> toReturn = new HashSet<String>();
		
		for(String loc : initialLocs){
			toReturn.add(loc);
			toReturn.addAll(reachableOnly(pg, toReturn, loc));
		}
		
		return toReturn;
	}

	private Set<String> reachableOnly(ProgramGraph<String, String> pg, Set<String> toReturn, String loc) {
		Set<PGTransition<String, String>> transitions = pg.getTransitions();
		
		boolean flag = false;
		
		for(PGTransition<String, String> trans : transitions){
			if(trans.getFrom().equals(loc) ){
				flag = true;
				if(!toReturn.contains(trans.getTo())){
					toReturn.add(trans.getTo());
					reachableOnly(pg, toReturn, trans.getTo());
				}
			}
		}
		if(flag == false){
			return toReturn;
		}
		return toReturn;
	}

	private HashSet<String> sub(StmtContext root, HashSet<String> loc, ProgramGraph<String, String> pg) {
		
		if(root.assstmt() != null|| root.chanreadstmt() != null|| root.chanwritestmt() != null||
				root.atomicstmt() != null||root.skipstmt() != null){
			loc.add("");
			loc.add(root.getText());
			
			if(root.assstmt() != null || root.chanreadstmt() != null || root.chanwritestmt() != null){
				PGTransition<String, String> t = new PGTransition<String, String>(root.getText(), "", root.getText(), "");
				pg.addTransition(t);
			}
			else if(root.atomicstmt() != null){
				
				PGTransition<String, String> t = new PGTransition<String, String>(root.getText(), "", root.getText(), "");
				pg.addTransition(t);
			}
			else if(root.skipstmt() != null){
				PGTransition<String, String> t = new PGTransition<String, String>(root.getText(), "", "skip", "");
				pg.addTransition(t);
			}
		}
		
		else if(root.ifstmt() != null){
//			System.out.println(root.);
			loc.add(root.getText());
			
			List<OptionContext> options = root.ifstmt().option();
			
			for(OptionContext option  : options){
				HashSet<String> emptyLoc = new HashSet<String>();
				loc.addAll(sub(option.stmt() , emptyLoc, pg));				
			}
			
			Set<PGTransition<String, String>> transitions = pg.getTransitions(); //trans so far
			
			for(OptionContext option  : options){
				String fromToCheck = option.stmt().getText();
				
				for(PGTransition<String, String> trans : transitions){
					if (trans.getFrom().equals(fromToCheck)){
						PGTransition<String, String> t;
						if(! (trans.getCondition().equals(""))){
							t = new PGTransition<String, String>(root.getText(),"(" + option.boolexpr().getText()  + ") && (" + trans.getCondition() +")" , trans.getAction() , trans.getTo() );
						}
						else{
							t =	new PGTransition<String, String>(root.getText(),"(" + option.boolexpr().getText()  +")" , trans.getAction() , trans.getTo() );
						}
						pg.addTransition(t);
					}
				}
			}
			
		}
		
		else if (root.dostmt() != null){
			loc.add(root.getText());
			loc.add("");
			
			List<OptionContext> options = root.dostmt().option();
			for(OptionContext option  : options){ //need to check if .stmt() is needed
				HashSet<String> emptyLoc = new HashSet<String>();
				HashSet<String> temp =  sub(option.stmt() , emptyLoc, pg);
				temp.remove("");
				
				String loopStmtWithSpaces =  addSpaces(root.getText());
				for(String str : temp){
					loc.add(str + ";" + root.getText());
					
					String strWithSpaces = addSpaces(str);
					String s = strWithSpaces + " ; " + loopStmtWithSpaces;
					StmtContext secondRoot= NanoPromelaFileReader.pareseNanoPromelaString(s);
					
					addAdditionalTransactions(secondRoot, pg);
				}
			}
			//first cond
			String allRules = "(";
			for(OptionContext option : options){
				allRules = allRules + option.boolexpr().getText() + ")||("; 
			}
			allRules= allRules.substring(0, allRules.length() - 3);
			PGTransition<String, String> t = new PGTransition<String, String>(root.getText(), "!("+allRules+")", "", "");
			pg.addTransition(t);
			
			//second cond
			Set<PGTransition<String, String>> transitions = pg.getTransitions();
			
			for(OptionContext option  : options){
				String fromToCheck = option.stmt().getText();
				
				for(PGTransition<String, String> trans : transitions){
					if (trans.getFrom().equals(fromToCheck) && trans.getTo().equals("")){
						PGTransition<String, String> t2;
						if(! (trans.getCondition().equals(""))){
							t2 = new PGTransition<String, String>(root.getText(),"(" + option.boolexpr().getText()  + ") && (" + trans.getCondition() +")" , trans.getAction() , root.getText() );
						}
						else{
							t2 = new PGTransition<String, String>(root.getText(),"(" + option.boolexpr().getText()  +")" , trans.getAction() , root.getText() );
						}
						pg.addTransition(t2);
					}
					
					else if (trans.getFrom().equals(fromToCheck) && !(trans.getTo().equals(""))){
						PGTransition<String, String> t2;
						if(! (trans.getCondition().equals(""))){
							t2 = new PGTransition<String, String>(root.getText(),"(" + option.boolexpr().getText()  + ") && (" + trans.getCondition() +")" , trans.getAction() ,trans.getTo()+";"+ root.getText() );
						}
						else{
							t2 =	new PGTransition<String, String>(root.getText(),"(" + option.boolexpr().getText()  +")" , trans.getAction() , trans.getTo()+";"+ root.getText() );
						}
						pg.addTransition(t2);
					}
				}
			}
			
		}
		
		else{ // ;
			HashSet<String> emptyLoc1 = new HashSet<String>();
			loc.addAll( sub(root.stmt(1) , emptyLoc1 , pg) );
			
			HashSet<String> emptyLoc0 = new HashSet<String>();
			HashSet<String> temp =  sub(root.stmt(0) , emptyLoc0, pg);
			temp.remove("");
			String secondStmtWithSpaces =  addSpaces(root.stmt(1).getText());
			
			for(String str : temp){
							
				loc.add(str + ";" + root.stmt(1).getText());
				
				String strWithSpaces = addSpaces(str);
				String s = strWithSpaces + " ; " + secondStmtWithSpaces;
				StmtContext secondRoot= NanoPromelaFileReader.pareseNanoPromelaString(s);
				
				addAdditionalTransactions(secondRoot, pg);
				
			}
			
			Set<PGTransition<String, String>> transitions = pg.getTransitions();
			
			for(PGTransition<String, String> trans : transitions){
				String toCheck = root.stmt(0).getText();
				if(trans.getFrom().equals(toCheck) && trans.getTo().equals("")){
					PGTransition<String, String> t = 
							new PGTransition<String, String>(root.getText(), trans.getCondition(), trans.getAction(), root.stmt(1).getText());
					pg.addTransition(t);
				}
				else if(trans.getFrom().equals(toCheck) && !(trans.getTo().equals(""))){
					PGTransition<String, String> t = 
							new PGTransition<String, String>(root.getText(), trans.getCondition(), trans.getAction(), trans.getTo()+";"+root.stmt(1).getText());
					pg.addTransition(t);
				}
			}
		}
		
		return loc;
	}
	
	

	
		
	

	private void addAdditionalTransactions(StmtContext secondRoot, ProgramGraph<String, String> pg) {
		Set<PGTransition<String, String>> transitions = pg.getTransitions();
		
		for(PGTransition<String, String> trans : transitions){
			String toCheck = secondRoot.stmt(0).getText();
			if(trans.getFrom().equals(toCheck) && trans.getTo().equals("")){
				PGTransition<String, String> t = 
						new PGTransition<String, String>(secondRoot.getText(), trans.getCondition(), trans.getAction(), secondRoot.stmt(1).getText());
				pg.addTransition(t);
			}
			else if(trans.getFrom().equals(toCheck) && !(trans.getTo().equals(""))){
				PGTransition<String, String> t = 
						new PGTransition<String, String>(secondRoot.getText(), trans.getCondition(), trans.getAction(), trans.getTo()+";"+secondRoot.stmt(1).getText());
				pg.addTransition(t);
			}
		}
		
	}

	private String addSpaces(String str) {
		str = str.replace("nsoda", "sagivmapgavker");
		str = str.replace("fi", " fi");
		str = str.replace("if", "if ");
		str = str.replace("od", " od");
		str = str.replace("do", "do ");
		str = str.replace("::", ":: ");
		
		
		str = str.replace("->", " -> ");
		str = str.replace("skip", " skip");
		str = str.replace("atomic", "atomic ");
		str = str.replace("sagivmapgavker", "nsoda");
		return str;
	}
//
    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
    	StmtContext root= NanoPromelaFileReader.pareseNanoPromelaString(nanopromela);
		ProgramGraph<String, String> pg = pgFromRoot(root);

		return pg;
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
    	StmtContext root= NanoPromelaFileReader.parseNanoPromelaStream(inputStream);
		ProgramGraph<String, String> pg = pgFromRoot(root);

		return pg;    }

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
