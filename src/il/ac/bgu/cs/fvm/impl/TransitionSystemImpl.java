package il.ac.bgu.cs.fvm.impl;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.exceptions.*;

public class TransitionSystemImpl<STATE, ACTION, ATOMIC_PROPOSITION> implements TransitionSystem<STATE, ACTION, ATOMIC_PROPOSITION> {

	private String name;
	private Set<ACTION> actions = new HashSet<ACTION>();
	private Set<STATE> initialStates = new HashSet<STATE>();
	private Set<STATE> states = new HashSet<STATE>();
	private Set<Transition<STATE, ACTION>> transitions= new HashSet<Transition<STATE, ACTION>>();
	private Set<ATOMIC_PROPOSITION> atomicPropositions = new HashSet<ATOMIC_PROPOSITION>();
	private Map<STATE, Set<ATOMIC_PROPOSITION>>labels = new HashMap<STATE, Set<ATOMIC_PROPOSITION>>();
	
	@Override
	public String getName() {
		return this.name;
	}

	@Override
	public void setName(String name) {
		this.name = name;
		
	}

	@Override
	public void addAction(ACTION action) {
		this.actions.add(action);
		
	}

	@Override
	public void addInitialState(STATE state) throws FVMException {
		if(this.states.contains(state))
			this.initialStates.add(state);
		else
			throw new InvalidInitialStateException(state);
		

	}

	@Override
	public void addState(STATE state) {
		this.states.add(state);
		this.labels.put(state, new HashSet<ATOMIC_PROPOSITION>());
		
	}

	@Override
	public void addTransition(Transition<STATE, ACTION> t) throws FVMException {
		if(this.states.contains(t.getTo()) && this.states.contains(t.getFrom()) && this.actions.contains(t.getAction()))
			this.transitions.add(t);
		else
			throw new InvalidTransitionException(t);
		
	}

	@Override
	public Set<ACTION> getActions() {
		return this.actions;
	}

	@Override
	public void addAtomicProposition(ATOMIC_PROPOSITION p) {
		this.atomicPropositions.add(p);
		
	}

	@Override
	public Set<ATOMIC_PROPOSITION> getAtomicPropositions() {
		return this.atomicPropositions;
	}

	@Override
	public void addToLabel(STATE s, ATOMIC_PROPOSITION l) throws FVMException {
		if(!this.states.contains(s) || !this.atomicPropositions.contains(l))
			throw new InvalidLablingPairException(s,l);
		if(this.labels.containsKey(s))
			this.labels.get(s).add(l);
		else {
			Set<ATOMIC_PROPOSITION> genratedSet = new HashSet<ATOMIC_PROPOSITION>();
			genratedSet.add(l);
			this.labels.put(s,genratedSet);
		}
		
	}

	@Override
	public Set<ATOMIC_PROPOSITION> getLabel(STATE s) {
		if(this.labels.containsKey(s))
			return this.labels.get(s);
		else
			throw new StateNotFoundException(s);
		
	}

	@Override
	public Set<STATE> getInitialStates() {
		return this.initialStates;
	}

	@Override
	public Map<STATE, Set<ATOMIC_PROPOSITION>> getLabelingFunction() {
		return this.labels;
	}

	@Override
	public Set<STATE> getStates() {
		return this.states;
	}

	@Override
	public Set<Transition<STATE, ACTION>> getTransitions() {
		return this.transitions;
	}

	@Override
	public void removeAction(ACTION action) throws FVMException {
		boolean isInTransition = false;
		for(Transition t : this.transitions) {
			isInTransition = t.getAction().equals(action) || isInTransition;
		}
		if(!isInTransition)
			this.transitions.remove(action);
		else
			throw new DeletionOfAttachedActionException(action,TransitionSystemPart.TRANSITIONS);
		
	}

	@Override
	public void removeAtomicProposition(ATOMIC_PROPOSITION p) throws FVMException {
		boolean isLabel = false;
		for(Set<ATOMIC_PROPOSITION> ap : this.labels.values()) {
			isLabel = ap.contains(p) || isLabel;
		}
		if(!isLabel)
			this.atomicPropositions.remove(p);
		else
			throw new DeletionOfAttachedAtomicPropositionException(p,TransitionSystemPart.LABELING_FUNCTION);
		
	}

	@Override
	public void removeInitialState(STATE state) {
		this.initialStates.remove(state);
		if(this.labels.get(state).size() == 0)
		{
			boolean isInTransition = false;
			for(Transition t : this.transitions) {
				isInTransition = t.getFrom().equals(state) || t.getTo().equals(state) || isInTransition;
			}
			if(!isInTransition) {
				this.states.remove(state);
				this.labels.remove(state);
			}
			
		}
		
	}

	@Override
	public void removeLabel(STATE s, ATOMIC_PROPOSITION l) {
		this.labels.get(s).remove(l);
		if(this.labels.get(s).size() == 0)
		{
			this.states.remove(s);
			this.initialStates.remove(s);
			this.labels.remove(s);
		}
		
		
	}

	@Override
	public void removeState(STATE state) throws FVMException {
		boolean isInTransition = false;
		for(Transition t : this.transitions) {
			isInTransition = t.getFrom().equals(state) || t.getTo().equals(state) || isInTransition;
			if(isInTransition)
				throw new DeletionOfAttachedStateException(state,TransitionSystemPart.TRANSITIONS);
		}
		if(this.initialStates.contains(state))
			throw new DeletionOfAttachedStateException(state,TransitionSystemPart.INITIAL_STATES);
		else if(this.labels.containsKey(state))
			throw new DeletionOfAttachedStateException(state,TransitionSystemPart.LABELING_FUNCTION);
		else {
			this.states.remove(state);
			this.initialStates.remove(state);
			this.labels.remove(state);
		}
		
	}

	@Override
	public void removeTransition(Transition<STATE, ACTION> t) {
		this.transitions.remove(t);
		
	}

}
