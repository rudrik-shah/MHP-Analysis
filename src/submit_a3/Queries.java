package submit_a3;

import java.util.HashMap;
import java.util.HashSet;

import dont_submit.MhpQuery;
import soot.Local;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.Stmt;

public class Queries {

	PEG p;
	
	Queries(PEG p1){
		
		p = p1;
	}
	
	void QueriesIterate() {
		
		for(int i = 0; i < A3.queryList.size(); i++) {
        	
			boolean ans = false;
			
        	MhpQuery q = A3.queryList.get(i);
        	
        	String var = q.getVar();
        	String field = q.getField();
        	
        	HashMap<Nodes, String> nodes = new HashMap<>();
        	
        	HashMap<Nodes, HashSet<String>> p2setOp = new HashMap<>();
        	
        	for(Nodes n : p.peg.keySet()) {
        		
        		Unit u = n.unit;
        		Stmt s = (Stmt) u;
        		
        		if(s instanceof DefinitionStmt) {
        			
        			DefinitionStmt ds = (DefinitionStmt) s;
        		
        			Value leftOp = ds.getLeftOp();
        			Value rightOp = ds.getRightOp();
        			
        			if(leftOp instanceof InstanceFieldRef) {
						
						Value varName = ((InstanceFieldRef)leftOp).getBase();
        				SootField f = ((InstanceFieldRef)leftOp).getField();
						
        				if(var.equals(varName.toString())) {
							
        					if(field.equals(f.getName())) {
								
        						p2setOp.put(n, p.findPointsToList((Local)varName));
								nodes.put(n, "w");
							}
        				}
        			}
        			
        			else if(rightOp instanceof InstanceFieldRef) {
        				
        				Value varName = ((InstanceFieldRef)rightOp).getBase();
        				SootField f = ((InstanceFieldRef)rightOp).getField();
						
        				if(var.equals(varName.toString())) {
							
        					if(field.equals(f.getName())) {
								
        						p2setOp.put(n, p.findPointsToList((Local)varName));
								nodes.put(n, "r");
							}
        				}
        			}
        		}
        	}
        	
        	for(Nodes node : nodes.keySet()) {
        		
        		HashSet<Nodes> mSet = p.mSet.get(node);
        		
        		for(Nodes n : mSet) {
        			
        			Unit u = n.unit;
        			Stmt s = (Stmt)u;
        			
        			if(s instanceof DefinitionStmt) {
            			
            			DefinitionStmt ds = (DefinitionStmt) s;
            		
            			Value leftOp = ds.getLeftOp();
            			Value rightOp = ds.getRightOp();
            			
            			if(leftOp instanceof InstanceFieldRef) {
            				
            				Value varName = ((InstanceFieldRef)leftOp).getBase();
            				SootField f = ((InstanceFieldRef)leftOp).getField();
            				
            				if(field.equals(f.getName())) {
            					
            					HashSet<String> p2setVar = p.findPointsToList((Local)varName);
            					HashSet<String> p2set = p2setOp.get(node);
            					
            					if(p.HasIntersection(p2setVar, p2set)) {
            						
            						ans = true;
            						break;
            					}
            				}
            			}
            			
            			else if(rightOp instanceof InstanceFieldRef) {
            				
            				Value varName = ((InstanceFieldRef)rightOp).getBase();
            				SootField f = ((InstanceFieldRef)rightOp).getField();
            				
            				if(field.equals(f.getName())) {
            					
            					HashSet<String> p2setVar = p.findPointsToList((Local)varName);
            					HashSet<String> p2set = p2setOp.get(node);
            					
            					if((p.HasIntersection(p2setVar, p2set)) && (nodes.get(node).equals("w"))) {
            						
            						ans = true;
            						break;
            					}
            				}
            			}
        			}
        		}
        	}
        	
        	if(ans) {
        	
        		A3.answers[i] = "Yes";
        	}
        	else {
        		
        		A3.answers[i] = "No";
        	}
        }

	}
}