package submit_a3;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import soot.Local;
import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.InvokeStmt;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.spark.pag.Node;
import soot.jimple.spark.sets.P2SetVisitor;
import soot.jimple.spark.sets.PointsToSetInternal;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.util.Chain;

class Nodes{
	
	HashSet<String> object;
	Unit unit;
	String 	thread;
	String specialProperty;
	
	Nodes(){
		
	}
	
	Nodes(HashSet<String> obj, Unit u, String t, String s){
		object = obj;
		unit = u;
		thread = t;	
		specialProperty = s;
	}
	
	void PrintNode() {
		System.out.println(object + " --- " + unit + " --- " + thread + " --- " + specialProperty);
	}
}

// Stores info for edges, target node and edge type
class Edges{
	
	Nodes targetNode;
	String edgeType;
	
	Edges(){
		
	}
	
	Edges(Nodes t, String eType){
		targetNode = t;
		edgeType = eType;
	}
}


public class PEG {
	
	// Program Execution Graph
	HashMap<Nodes, HashSet<Edges>> peg;
	
	HashMap<Nodes, HashSet<Edges>> predPeg;
	
	PointsToAnalysis pta;
	
	static HashMap<Node, String> objects;
	
	Nodes beginNodeMain;
	
	Chain<SootClass> allClasses;
	ArrayList<SootMethod> allMethods;
	
	// Count variable for creating unique thread id's
	int tID = 0;
	
	HashMap<Nodes, HashSet<Nodes>> mSet;
	
	HashMap<Nodes, HashSet<Nodes>> outSet;
	
	HashMap<Nodes, HashSet<Nodes>> notifySuccSet;
	
	HashMap<Nodes, HashSet<Nodes>> genSet;
	
	HashMap<Nodes, HashSet<Nodes>> genNotifyAllSet;
	
	HashMap<Nodes, HashSet<Nodes>> killSet;
	
	PEG(){
		
		peg = new HashMap<>();
		predPeg = new HashMap<>();
		
		// Finding all the classes and methods in the program
		allClasses = Scene.v().getApplicationClasses();
		
		allMethods = new ArrayList<>();
		
		for(SootClass c : allClasses) {
			
			if(!c.isLibraryClass()) {
			
				List<SootMethod> methods = c.getMethods();
				
				for(SootMethod m : methods) {
					
					if(!m.isConstructor()) {
						
						allMethods.add(m);
					}
				}
			}
		}
	}
	
	void Dfs(Nodes node, HashSet<Nodes> visited, HashSet<Nodes> set) {
		
		visited.add(node);
		
		Iterator<Edges> it;
		if(peg.containsKey(node)) {
			
			it = peg.get(node).iterator();
			while(it.hasNext()) {
				
				Edges succ = it.next();
				
				if(isExit(succ.targetNode.unit)) {
					
					break;
				}
				
				if(! visited.contains(succ.targetNode)) {
					
					set.add(succ.targetNode);
					Dfs(succ.targetNode, visited, set);
				}
			}
		}
	}
	
	// To find the list of references pointed by the variable
	HashSet<String> findPointsToList(Local l) {

        // Initialize an empty array list
        HashSet<String> listOfObjs = new HashSet<>();
        
        PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
        PointsToSet pts = pta.reachingObjects(l);
        PointsToSetInternal pti = (PointsToSetInternal) pts;

        P2SetVisitor vis = new P2SetVisitor() {

            @Override
            public void visit(Node n) {
            	
            	String s = new String("Obj " + n.getType() + n.getNumber());
                listOfObjs.add(s);
            }

        };
        pti.forall(vis);

        return listOfObjs;
    }
	
	String FindThreadID(SootMethod method) {
		if(method.isMain()) {
			return "Main";
		}
		else {
			tID++;
			return ("T" + tID);
		}
	}
	
	void PopulateGraph(SootMethod method, Nodes caller) {
		
		String tId = FindThreadID(method);
		UnitGraph g = new BriefUnitGraph(method.getActiveBody());
	
		HashMap<Unit, Nodes> unitNodeMap = new HashMap<>();
		
		HashSet<String> p2Set = new HashSet<>();
		
		if(caller.unit != null) {
			
			Stmt stmt = (Stmt)caller.unit;
			VirtualInvokeExpr vExpr = (VirtualInvokeExpr)stmt.getInvokeExpr();
			Value baseVal = vExpr.getBase();
			
			p2Set = findPointsToList((Local)baseVal);
		}
		
		// Iterate over all nodes of the method and create a PEG node for them and store 
		for(Unit u : g) {
			
			Nodes newNode = new Nodes(new HashSet<>(p2Set), u, tId, "");
			
			unitNodeMap.put(u, newNode);
			
			peg.put(newNode, new HashSet<>());
		}
		
		// Add begin node in PEG and its edges
		Unit unit = g.getHeads().get(0);
		
		Nodes beginNode = new Nodes(new HashSet<>(), null , tId, "Begin Node");
		HashSet<Edges> begin = new HashSet<>();
		begin.add(new Edges(unitNodeMap.get(unit),"Local Edge"));
		peg.put(beginNode , begin);
		
		// Add edge from caller node to begin node
    	if(!tId.equals("Main")) {
    	
    		peg.get(caller).add(new Edges(beginNode,"Local Edge"));
    	}
    	else {
    		
    		beginNodeMain = beginNode;
    	}
		
    	// Add end node
    	for(Unit u: g){
    		
    		if(g.getSuccsOf(u).isEmpty()) {
    			
    			Nodes endNode = new Nodes(new HashSet<>(), null , tId, "End Node");
    			HashSet<Edges> end = new HashSet<>();
    			end.add(new Edges(endNode, "Local Edge"));
    			peg.put(unitNodeMap.get(u) , end);
    		}	
    	}
    	
    	// Add start node and make PEG for its run method and create 3 nodes for wait unit
    	for(Unit u : g) {
    		
    		Stmt s = (Stmt)u;
    		
    		// Add start node and make PEG for its run method
    		if(isStart(u)) {
    			
    			HashSet<String> p2set = new HashSet<>();
    			VirtualInvokeExpr vExp = (VirtualInvokeExpr)s.getInvokeExpr();
    			Value baseVar = vExp.getBase();
    			Type baseClass = baseVar.getType();
    			
    			p2set = findPointsToList((Local)baseVar);
    			
    			Nodes sNode = unitNodeMap.get(u);
    			sNode.object = p2set;
    			
    			for(SootMethod m : allMethods) {
    				
    				if(m.getDeclaringClass().getName().equals(baseClass.toString())) {
    					
    					PopulateGraph(m, sNode);
    					break;
    				}
    			}
    		}
    		
    		// Create 3 nodes for wait unit 
    		else if(isWait(u)) {
    			
    			VirtualInvokeExpr vExp = (VirtualInvokeExpr)s.getInvokeExpr();
    			Value baseVar = vExp.getBase();
    			
    			HashSet<String> p2set = findPointsToList((Local)baseVar);
    			
    			Nodes waitNode = unitNodeMap.get(u);
    			waitNode.object = p2Set;
    			waitNode.specialProperty = "Wait Node";
    			
    			Nodes waitingNode = new Nodes(p2set, null, tId, "Waiting Node");
    			
    			Nodes notifiedEntry = new Nodes(p2set, null, tId, "Notified Entry Node");
    			
    			peg.put(waitingNode, new HashSet<>());
    			peg.put(notifiedEntry, new HashSet<>());
    			
    			List<Unit> succ = g.getSuccsOf(u);
    			for(Unit u1 : succ) {
    				
    				Nodes tgt = unitNodeMap.get(u1);
    				peg.get(notifiedEntry).add(new Edges(tgt, "Local Edge"));
    			}
    			
    			peg.get(waitNode).add(new Edges(waitingNode, "Local Edge"));
    			peg.get(waitingNode).add(new Edges(notifiedEntry, "Waiting Edge"));
    		}
    		
    		else if(isEntry(u)) {
    			
    			EnterMonitorStmt e = (EnterMonitorStmt)s;
    			Value baseVar = e.getOp();
    			
    			HashSet<String> p2set = findPointsToList((Local)baseVar);
    			
    			Nodes node = unitNodeMap.get(u);
    			node.object = p2Set;
    		}
    		
    		else if(isExit(u)) {
    			
    			ExitMonitorStmt e = (ExitMonitorStmt)s;
    			Value baseVar = e.getOp();
    			
    			HashSet<String> p2set = findPointsToList((Local)baseVar);
    			
    			Nodes node = unitNodeMap.get(u);
    			node.object = p2Set;
    		}
    		
    		else if(isNotify(u)) {
    			
    			VirtualInvokeExpr vExp = (VirtualInvokeExpr)s.getInvokeExpr();
    			Value baseVar = vExp.getBase();
    			
    			HashSet<String> p2set = findPointsToList((Local)baseVar);
    			
    			Nodes waitNode = unitNodeMap.get(u);
    			waitNode.object = p2Set;    		
    		}
    		
    		else if(isNotifyAll(u)) {
    			
    			VirtualInvokeExpr vExp = (VirtualInvokeExpr)s.getInvokeExpr();
    			Value baseVar = vExp.getBase();
    			
    			HashSet<String> p2set = findPointsToList((Local)baseVar);
    			
    			Nodes waitNode = unitNodeMap.get(u);
    			waitNode.object = p2Set;    		
    		}
    		
    		else if(isJoin(u)) {
    			
    			VirtualInvokeExpr vExp = (VirtualInvokeExpr)s.getInvokeExpr();
    			Value baseVar = vExp.getBase();
    			
    			HashSet<String> p2set = findPointsToList((Local)baseVar);
    			
    			Nodes waitNode = unitNodeMap.get(u);
    			waitNode.object = p2Set;    		
    		}
    	}
    	
    	// Add normal CFG edges in PEG
		for(Unit u : g) {
			
			if(!isWait(u)) {
				
				List<Unit> successors = g.getSuccsOf(u);
				String e = "Local Edge";
				
				for(Unit succ : successors) {
					
					Nodes src = unitNodeMap.get(u);
					Nodes tgt = unitNodeMap.get(succ);
					
					Edges edge = new Edges(tgt, e);
					
					peg.get(src).add(edge);
				}
			}
		}
	}
		
	// To store the predecessors of nodes in predPeg graph
	void ReversePeg() {
		
		for(Nodes node : peg.keySet()) {
			
			predPeg.put(node, new HashSet<>());
		}
		
		for(Map.Entry<Nodes, HashSet<Edges>> entry : peg.entrySet()) {
			
			Nodes node = entry.getKey();
			HashSet<Edges> succ = entry.getValue();
			
			for(Edges s : succ) {
				
				Edges pred = new Edges(node, s.edgeType);
				
				if(! predPeg.containsKey(s.targetNode)) {
					
					HashSet<Edges> p = new HashSet<>();
					p.add(pred);
					predPeg.put(s.targetNode, p);
				}
				else {
					
					predPeg.get(s.targetNode).add(pred);
				}
			}
		}
	}
	
	void InitializeSets() {
		
		mSet = new HashMap<>();
		outSet = new HashMap<>();
		genSet = new HashMap<>();
		killSet = new HashMap<>();
		
		notifySuccSet = new HashMap<>();
		genNotifyAllSet = new HashMap<>();
		
		for(Nodes node : peg.keySet()) {
			
			mSet.put(node, new HashSet<>());
			outSet.put(node, new HashSet<>());
			genSet.put(node, new HashSet<>());
			killSet.put(node, new HashSet<>());
			
			notifySuccSet.put(node, new HashSet<>());
			genNotifyAllSet.put(node, new HashSet<>());
		}
	}
	
	// Returns true if unit is a start unit
    boolean isStart(Unit u) {

    	if(u != null) {
	        
    		if (((Stmt) u) instanceof InvokeStmt) {
	        	
	            if (((Stmt) u).getInvokeExpr() instanceof VirtualInvokeExpr) {
	             
	            	if (((VirtualInvokeExpr)((Stmt) u).getInvokeExpr()).getMethod().toString().equals("<java.lang.Thread: void start()>")) {
	                 
	            		return true;
	            	}
	            }
	        }
    	}

        return false;
    }

    // Returns true if unit is join unit
    boolean isJoin(Unit u) {

    	if(u != null) {
	        
    		if (((Stmt) u) instanceof InvokeStmt) {
	        	
	            if (((Stmt) u).getInvokeExpr() instanceof VirtualInvokeExpr) {
	            	
	                if (((VirtualInvokeExpr)((Stmt) u).getInvokeExpr()).getMethod().toString().equals("<java.lang.Thread: void join()>")) {
	                 
	                	return true;
	                }
	            }
	        }
    	}
    	
        return false;

    }

    // Returns true if enterMonitor statement
    boolean isEntry(Unit u) {

    	if(u != null) {
	        
    		if (((Stmt) u) instanceof EnterMonitorStmt) {
	         
	        	return true;
	        }
    	}

        return false;

    }

    // Returns true if exitMonitor statement
    Boolean isExit(Unit u) {

    	if(u != null) {
        
    		if (((Stmt) u) instanceof ExitMonitorStmt) {
         
    			return true;
    		}
    	}

        return false;

    }

    Boolean isNotify(Unit u) {

    	if(u != null) {
        
    		if (((Stmt) u) instanceof InvokeStmt) {
            
    			if (((Stmt) u).getInvokeExpr() instanceof VirtualInvokeExpr) {
            
    				if (((VirtualInvokeExpr)((Stmt) u).getInvokeExpr()).getMethod().toString().equals("<java.lang.Object: void notify()>")) {
                
    					return true;
    				}
    			}
    		}
    	}
    	
        return false;

    }

    Boolean isNotifyAll(Unit u) {

    	if(u != null) {
        
    		if (((Stmt) u) instanceof InvokeStmt) {
            
    			if (((Stmt) u).getInvokeExpr() instanceof VirtualInvokeExpr) {
            
    				if (((VirtualInvokeExpr)((Stmt) u).getInvokeExpr()).getMethod().toString().equals("<java.lang.Object: void notifyAll()>")) {
                
    					return true;
    				}
    			}
    		}
    	}

        return false;

    }

    Boolean isWait(Unit u) {

    	if(u != null) {
        
    		if (((Stmt) u) instanceof InvokeStmt) {
            
    			if (((Stmt) u).getInvokeExpr() instanceof VirtualInvokeExpr) {
            
    				if (((VirtualInvokeExpr)((Stmt) u).getInvokeExpr()).getMethod().toString().equals("<java.lang.Object: void wait()>")) {
                
    					return true;
    				}
    			}
    		}
    	}
    		
        return false;

    }
	
	// To return the waiting predecessor of Notified Entry node
	Nodes WaitingPred(Nodes node) {
		
		for(Edges edge: predPeg.get(node)){
			
			if(edge.targetNode.specialProperty.equals("Waiting Node")) {
				
				return edge.targetNode;
			}
		}
		
		return null;
	}
	
	// To return start predecessors of the begin node of run method
	HashSet<Nodes> StartPred(Nodes node){
		
		HashSet<Nodes> startPreds = new HashSet<>();
		
		for(Edges edge: predPeg.get(node)){
		
			if(edge.targetNode.specialProperty.equals("Start Node")) {
				
				startPreds.add(edge.targetNode);
			}
		}
		return startPreds;
	}
	
	// Return all nodes of a thread
	HashSet<Nodes> AllNodes(String tId){
		
		HashSet<Nodes> allNodes = new HashSet<>();

        for(Nodes node: peg.keySet()) {
         
        	if(node.thread.equals(tId)) {
            
        		allNodes.add(node);
        	}
        }

        return allNodes;
	}
	
	HashSet<Nodes> WaitingNodes(String obj){
		
		HashSet<Nodes> waitingNodes = new HashSet<>();
    	
    	for(Nodes n : peg.keySet()) { 
    		
    		if(n.specialProperty.equals("Waiting") && n.object.contains(obj)) { 
    		
    			waitingNodes.add(n);
    		}
    	}
    
    	return waitingNodes;
	}
	
	HashSet<Nodes> BeginSucc(Nodes node) {

        HashSet<Nodes> beginSuccs = new HashSet<Nodes>();

        for(Edges succ: peg.get(node)) {

            if (succ.targetNode.specialProperty.equals("Begin Node")) {
             
            	beginSuccs.add(succ.targetNode);
            }
        }

        return beginSuccs;
    }
	
	HashSet<Nodes> NotifyPred(Nodes node) {

        HashSet<Nodes> notifyPreds = new HashSet<>();

        for (Edges p: predPeg.get(node)) {
         
        	if (p.targetNode.specialProperty.equals("Notify Node") || p.targetNode.specialProperty.equals("Notify All Node")) {
             
        		notifyPreds.add(p.targetNode); 
        	}
        }

        return notifyPreds;
    }
	
	HashSet<Nodes> LocalPred(Nodes node) {

        HashSet<Nodes> localPreds = new HashSet<>();

        for (Edges p: predPeg.get(node)) {
         
        	if (p.edgeType.equals("Local Edge")) {
             
        		localPreds.add(p.targetNode);
        	}
        }

        return localPreds;
    }
	
	// Compute Union of two sets
    HashSet<Nodes> Union(HashSet<Nodes> set1, HashSet<Nodes> set2) {

        HashSet<Nodes> union = new HashSet<>();

        union.addAll(set1);
        union.addAll(set2);

        return union;
    }

    // Compute difference of two sets (setA - setB)
    HashSet<Nodes> Difference(HashSet<Nodes> set1, HashSet<Nodes> set2) {

        HashSet<Nodes> difference = new HashSet<>();

        for (Nodes node: set1) {
        	
            if (!set2.contains(node)) {
             
            	difference.add(node);
            }
            
        }

        return difference;
    }
    
    // Check if two sets have something in common or not
 	boolean HasIntersection(HashSet<String> set1, HashSet<String> set2) {
 		
     	for(String obj: set1) {
     		
     		if(set2.contains(obj)) {
     		
     			return true;
     		}
     	}
     	
     	return false;
    }
 	
 	// Returns intersection of two sets
 	HashSet<Nodes> GetIntersection(HashSet<Nodes> set1, HashSet<Nodes> set2) {
 		
     	HashSet<Nodes> intersection = new HashSet<>();
     	
     	for(Nodes n : set1) {
     		
     		if(set2.contains(n)) {
     			
     			intersection.add(n);
     		}
     	}
     	
     	return intersection;
    }

    // Computing Out Set
    HashSet<Nodes> ComputeOut(Nodes node) {

    	HashSet<Nodes> m = mSet.get(node);
    	
    	HashSet<Nodes> union = Union(m, genSet.get(node));
    	HashSet<Nodes> kill = killSet.get(node);
    	
        return Difference(union, kill);
    }
    
    // Computing M Set
    HashSet<Nodes> ComputeM(Nodes node){
    	
    	HashSet<Nodes> updates = new HashSet<>();
    	
    	if(node.specialProperty.equals("Notified Entry Node")) {
    		
    		for(Nodes p :  NotifyPred(node)) { 
    		
    			HashSet<Nodes> o = outSet.get(p);
    			updates = Union(updates, o);
    		}
    		
    		Nodes w = WaitingPred(node);
    		HashSet<Nodes> o  = outSet.get(w);
    		updates = GetIntersection(updates, o);
    		
    		HashSet<Nodes> g = genNotifyAllSet.get(node);
    		updates = Union(updates, g);
    		
    		return Union(updates, mSet.get(node));	
    	}
    	
    	else if(node.specialProperty.equals("Begin Node")) { 
    		
    		for(Nodes p :  StartPred(node)) {
    		
    			HashSet<Nodes> o = outSet.get(p);
    			updates = Union(updates, o);
    		}
    		
    		HashSet<Nodes> a = AllNodes(node.thread);
    		updates = Difference(updates, a);
    		
    		return Union(updates, mSet.get(node));
    		
    	}
    	
    	for(Nodes p :  LocalPred(node)) {
		
    		HashSet<Nodes> o = outSet.get(p);
			updates = Union(updates, o);
    	}
    	
    	return Union(updates, mSet.get(node));
    }
    
    // Computing Gen Set
    HashSet<Nodes> ComputeGen(Nodes node) {

        if(isExit(node.unit)) {
        	for(Nodes nDash : AllNodes(node.thread)) {
        		
        		if(isEntry(nDash.unit) && HasIntersection(node.object, nDash.object)) { 
        			
        				return killSet.get(nDash);
        		}
        	}
        }
        
        else if(node.specialProperty.equals("Notify Node") || node.specialProperty.equals("Notify All Node")) {
            
        	return notifySuccSet.get(node); 
        }
        
        else if (isStart(node.unit)) {
            
        	return BeginSucc(node);
        }
        		
        return new HashSet<Nodes>();
    }
    
    // Computing Kill set
    HashSet<Nodes> ComputeKill(Nodes node){
    	
		if(isJoin(node.unit) && node.object.size() == 1) {  
    		
			return AllNodes(node.thread);
		}
    	
    	
    	if(this.isEntry(node.unit) || node.specialProperty.equals("Notified Entry Node")) { 
    		
    		if(node.object.size() == 1) { 
    			
    			HashSet<Nodes> visited = new HashSet<>();
    			HashSet<Nodes> set = new HashSet<>();
    			Dfs(node, visited, set);
    			
    			return set;
    		}
    	}
    	
    	if(node.specialProperty.equals("Notify All Node")) { 
    	
    		HashSet<Nodes> waitingNodes = new HashSet<Nodes> ();
    		
    		for(String obj : node.object) { 
    		
    			waitingNodes.addAll(WaitingNodes(obj));
    		}
    		
    		return waitingNodes;
    	}
    	
    	if(node.specialProperty.equals("Notify Node")) { 
    		
    		HashSet<Nodes> waitingNodes = new HashSet<>();
    		
    		for(String obj : node.object) { 
    			
    			if(WaitingNodes(obj).size() == 1) {
    			
    				waitingNodes.addAll(WaitingNodes(obj));
    			}
    		}
    		
    		return waitingNodes;
    	}
    		
        return new HashSet<Nodes>();
	}
    
    // To return notify successors of the Waiting node
 	HashSet<Nodes> ComputeNotifySucc(Nodes node){
 		
 		HashSet<Nodes> notifySuccs = new HashSet<>();
 		
 		HashSet<Nodes> m = mSet.get(node);  
 				
 		for(Nodes n : m) {
 			
 			if(n.specialProperty.equals("Waititng Node")) {
 				
 				HashSet<Edges> succ = peg.get(n);
 				Nodes notifiedEntryNode = succ.iterator().next().targetNode;
 				
 				if(notifiedEntryNode.specialProperty.equals("Notified Entry Node")) {
 					
 					if(node.object != null) {
 						
 						HashSet<String> intersection = new HashSet<>();
 						
 						for (String obj: node.object) {
 							
 	                        if (notifiedEntryNode.object.contains(obj)) {
 	                        	
 	                            intersection.add(obj);
 	                        }
 						}
 	                        
 	                    if (!intersection.isEmpty()) {
 	                     
 	                    	notifySuccs.add(notifiedEntryNode);
 	                    }
 					}
 				}
 			}
 		}
 		
 		return notifySuccs;
 	}
    
    HashSet<Nodes> ComputeGenNotifyAll(Nodes node){
		
		HashSet<Nodes> genNotifyAll = new HashSet<>();
    	
    	if(node.specialProperty.equals("Notified Entry Node")) {
    		
    		for(Nodes n: peg.keySet()) {
    			
    			if(n.specialProperty.equals("Notified Entry Node") && HasIntersection(node.object, n.object)) {
    				
    				HashSet<Nodes> mNode1 = mSet.get(WaitingPred(n));
    				HashSet<Nodes> mNode2 = mSet.get(WaitingPred(node));
    				
    				if(mNode2.contains(WaitingPred(n))) {
    					
    					for(Nodes r: peg.keySet()) {
    						
    						if(r.specialProperty.equals("Notify All Node")) {
    							
    							HashSet<Nodes> intersection = GetIntersection(mNode1, mNode2);
    							
    							if(intersection.contains(r)) {
    								
    								genNotifyAll.add(n);
    							}
    						}
    					}
    				}
    			}
    		}
    	}
    	
    	return genNotifyAll;
	}
	
	void PrintPeg(HashMap<Nodes, HashSet<Edges>> peg) {
		
		for(Entry<Nodes, HashSet<Edges>> entry : peg.entrySet()) {
			
			Nodes src = entry.getKey();
			HashSet<Edges> edge = entry.getValue();
			
			for(Edges e : edge) {
				
				Nodes tgt = e.targetNode;
				String eType = e.edgeType;
				
				src.PrintNode();
				System.out.println(eType);
				tgt.PrintNode();
				System.out.println();
				
			}
		}
	}
}