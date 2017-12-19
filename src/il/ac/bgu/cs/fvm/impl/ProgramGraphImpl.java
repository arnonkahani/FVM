package il.ac.bgu.cs.fvm.impl;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

public class ProgramGraphImpl<L, A> implements ProgramGraph<L, A> {

	private Set<L> locations;
    private Set<PGTransition<L, A>> transitions;
    private String name;
    private Set<List<String>> initalization;
    private Set<L> initialLocations;
    
    public ProgramGraphImpl()
    {
        locations = new HashSet<L>();
        initialLocations = new HashSet<L>();
        transitions = new HashSet<PGTransition<L, A>>();
        initalization = new HashSet<List<String>>();
    }
    
	@Override
	public void addInitalization(List<String> init) {
		initalization.add(init);
		
	}

	@Override
	public void addInitialLocation(L location) {
		this.addLocation(location);
        this.initialLocations.add(location);
		
	}

	@Override
	public void addLocation(L l) {
		this.locations.add(l);
		
	}
	
	
	
	@Override
	public void addTransition(PGTransition<L, A> t) {
		this.transitions.add(t);
		
	}

	@Override
	public Set<List<String>> getInitalizations() {
		return new HashSet<List<String>>(this.initalization);
	}

	@Override
	public Set<L> getInitialLocations() {
		return new HashSet<L>(this.initialLocations);
	}

	@Override
	public Set<L> getLocations() {
		return this.locations;
	}

	@Override
	public String getName() {
		return this.name;
	}

	@Override
	public Set<PGTransition<L, A>> getTransitions() {
		return new HashSet<PGTransition<L, A>>(this.transitions);
	}

	@Override
	public void removeLocation(L l) {
		this.initialLocations.remove(l);
        this.locations.remove(l);
		
	}

	@Override
	public void removeTransition(PGTransition<L, A> t) {
		this.transitions.remove(t);
		
	}

	@Override
	public void setName(String name) {
		this.name = name;
		
	}

}
