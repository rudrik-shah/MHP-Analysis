package submit_a3;

import java.util.HashSet;
import java.util.Map;

import soot.SceneTransformer;
import soot.SootMethod;

public class MhpAnalysis extends SceneTransformer{

	static int c;
	@Override
	protected void internalTransform(String phaseName, Map<String, String> options) {
		/*
		 * Implement your mhp analysis here
		 */
		
		// Constructing PEG with main method
		PEG p = new PEG();
		
		SootMethod method = p.allMethods.get(0);
		
		for(SootMethod m : p.allMethods) {
			
			if(m.isMain()) {
				method = m;
				break;
			}
		}
		
		Nodes caller = new Nodes(new HashSet<>(), null, "Compiler", "Main Caller");
		p.PopulateGraph(method, caller);
		
		p.ReversePeg();
		
		p.InitializeSets();
	
		IterateWorklist(p);

		Queries q = new Queries(p);
		q.QueriesIterate();
	}	
			
	void IterateWorklist(PEG p) {
				
			boolean flag = false;
			c++;
			
			for (Nodes node : p.peg.keySet()) { 

				// Update OUT
	    		HashSet<Nodes> newOut = p.ComputeOut(node);
	    		
	    		if(!(newOut.equals(p.outSet.get(node)))) {
	    			
	    			p.outSet.get(node).clear();
	    			p.outSet.put(node, newOut);
	    			
	    			flag = true;
	    		}
	    		
	    		// Update M
	    		HashSet<Nodes> newM = p.ComputeM(node);
	    		
	    		if(!(newM.equals(p.mSet.get(node)))) {
	    			
	    			p.mSet.get(node).clear();
	    			p.mSet.put(node, newM);
	    			
	    			for(Nodes m : newM) {
	    			
	    				p.mSet.get(m).add(node);
	    			}
	    			
	    			flag = true;
	    		}
	    		
	    		// Update GEN
	    		HashSet<Nodes> newGen = p.ComputeGen(node);
	    		
	    		if(!(newGen.equals(p.genSet.get(node)))) {
	    			
	    			p.genSet.get(node).clear();
	    			p.genSet.put(node, newGen);
	    			
	    			flag = true;
	    		}
	    		
	    		// Update KILL
	    		HashSet<Nodes> newKill = p.ComputeKill(node);
	    		
	    		if(!(newKill.equals((p.killSet.get(node))))) {
	    			
	    			p.killSet.get(node).clear();
	    			p.killSet.put(node, newKill);
	    			
	    			flag = true;
	    		}
	    		
				// Update NotifySucc
	    		HashSet<Nodes> newNotifySuccs = p.ComputeNotifySucc(node);
	    		
	    		if(!(newNotifySuccs.equals(p.notifySuccSet.get(node)))) {
	    			
	    			p.notifySuccSet.get(node).clear();
	    			p.notifySuccSet.put(node, newNotifySuccs);
	    			
	    			for(Nodes m : p.notifySuccSet.get(node)) {	
	    	    	
	    				p.peg.get(node).add(new Edges(m, "Notify -> Notified Entry Edge")); 
	    			}
	    	    	
	    	    	for(Nodes m : p.notifySuccSet.get(node)) {
	    	    	
	    	    		p.predPeg.get(m).add(new Edges(node, "Notify -> Notified Entry Edge")); 
	    	    	}
	    			
	    			flag = true;
	    		}
	    		
	    		// Update GENNotifyALL
	    		HashSet<Nodes> newGenNotifyAll = p.ComputeGenNotifyAll(node);
	    		
	    		if(!(newGenNotifyAll.equals(p.genNotifyAllSet.get(node)))) {
	    			
	    			p.genNotifyAllSet.get(node).clear();
	    			p.genNotifyAllSet.put(node,  newGenNotifyAll);
	    			
	    			flag = true;
	    		}
	        }
			
			if(flag) {
			
				IterateWorklist(p);
			}
	}	
}