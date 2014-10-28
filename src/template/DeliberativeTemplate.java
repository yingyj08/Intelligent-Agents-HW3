package template;

/* import table */
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.TreeMap;

import logist.simulation.Vehicle;
import logist.agent.Agent;
import logist.behavior.DeliberativeBehavior;
import logist.plan.Action;
import logist.plan.Plan;
import logist.task.Task;
import logist.task.TaskDistribution;
import logist.task.TaskSet;
import logist.topology.Topology;
import logist.topology.Topology.City;
import logist.plan.Action.Delivery;
import logist.plan.Action.Move;
import logist.plan.Action.Pickup;

/**
 * An optimal planner for one vehicle.
 */
@SuppressWarnings("unused")
public class DeliberativeTemplate implements DeliberativeBehavior {

	enum Algorithm { BFS, ASTAR, NAIVE }
	enum Heuristic { BASIC, DIAMETER, MST }
	
	private static final int WAITING = 0;
	private static final int PICKEDUP = 1;
	private static final int DELIVERED = 2;
	private Task[] taskList = null; //taskList[i] is state[i+1]
	private List<City> cityList;
	private int costPerKm;
	private int nCarried;
	private int nTasks;
	
	private ArrayList<Diameter> diameterList;
	
	/* Environment */
	Topology topology;
	TaskDistribution td;
	
	/* the properties of the agent */
	Agent agent;
	int capacity;

	/* the planning class */
	Algorithm algorithm;
	Heuristic heuristic;
	
	/* for MST heuristic */
	HashMap<MSTState, Double> mstTable;
	class MSTState{
		private boolean isCityAlive[];
		MSTState() {
			isCityAlive = new boolean[cityList.size()];
		}
		@Override
		public boolean equals(Object other) {
		    if (other == null) return false;
		    if (other == this) return true;
		    if (!(other instanceof MSTState))return false;
		    MSTState otherNode = (MSTState)other;
		    for (int i = 0; i < this.isCityAlive.length; ++i) {
		    	if (this.isCityAlive[i] != otherNode.isCityAlive[i])
		    		return false;
		    }
			return true;
		}
		@Override
		public int hashCode() {
			return Arrays.hashCode(isCityAlive);
		}
	}
	
	/* class for search algorithms */
	BitSet goalState;
	BitSet initState;
	class Node implements Comparable<Node>{
		private int curCityId;
		private BitSet taskState;
		private StateInfo stateInfo;
		private Node(){stateInfo = new StateInfo();}
		private Node(int curCityId, BitSet taskState, StateInfo stateInfo){
			this.curCityId = curCityId;
			this.taskState = taskState;
			this.stateInfo = stateInfo;
		}
		@Override
		public int compareTo(Node b) {
			if (this.stateInfo.cost < b.stateInfo.cost)
				return -1;
			if (this.stateInfo.cost > b.stateInfo.cost)
				return 1;
			return 0;
		}
		@Override
		public boolean equals(Object other) {
		    if (other == null) return false;
		    if (other == this) return true;
		    if (!(other instanceof Node))return false;
		    Node otherNode = (Node)other;
		    if (this.curCityId != otherNode.curCityId)
		    	return false;
		    if (!this.taskState.equals(otherNode.taskState))
		    	return false;
			return true;
		}
		@Override
		public int hashCode() {
			//JSHash
            int hash = 1315423911 ^ taskState.hashCode();
            hash ^= ((hash << 5) + curCityId + (hash >> 2));
            return hash;
		}
	}
	class StateInfo{
		private int preCityID = -1;
		private int targetTaskIndex = -1;
		private double cost = 0;
		private double pastCost = 0;
		private int curDiaId = 0;
		private StateInfo(){}
		private StateInfo(int preCityID, int targetTaskIndex, double cost, double pastCost, int curDiaId){
			this.preCityID = preCityID;
			this.targetTaskIndex = targetTaskIndex;
			this.cost = cost;
			this.pastCost = pastCost;
			this.curDiaId = curDiaId;
		}
		@Override
		public String toString(){
			StringBuilder sb = new StringBuilder();
			sb.append(preCityID);
			sb.append(' ');
			sb.append(targetTaskIndex);
			sb.append(' ');
			sb.append(cost);
			sb.append(' ');
			sb.append(pastCost);
			sb.append(' ');
			return sb.toString();
		}
	}
	
	class Diameter implements Comparable<Diameter>{
		private int x;
		private int y;
		private double distance;
		private Diameter(int x, int y, double distance) {
			this.x = x;
			this.y = y;
			this.distance = distance;
		}
		@Override
		public int compareTo(Diameter b) {
			if (this.distance > b.distance)
				return -1;
			if (this.distance > b.distance)
				return 1;
			return 0;
		}
	}
	
	@Override
	public void setup(Topology topology, TaskDistribution td, Agent agent) {
		this.topology = topology;
		this.td = td;
		this.agent = agent;
		// initialize the planner
		String algorithmName = agent.readProperty("algorithm", String.class, "ASTAR");
		String heuristicName = agent.readProperty("heuristic", String.class, "DIAMETER");
		
		// Throws IllegalArgumentException if algorithm is unknown
		algorithm = Algorithm.valueOf(algorithmName.toUpperCase());
		heuristic = Heuristic.valueOf(heuristicName.toUpperCase());
		
		// ...
		this.costPerKm = agent.vehicles().get(0).costPerKm();
		this.cityList = topology.cities();
		this.capacity = agent.vehicles().get(0).capacity();
	}
	
	@Override
	public Plan plan(Vehicle vehicle, TaskSet tasks) {
		//calculating time
		long start = System.currentTimeMillis();
		Plan plan = null;
		nCarried = vehicle.getCurrentTasks().size(); //update the #carried tasks
		nTasks = tasks.size();//update #left-over tasks
		//update taskList: remaining tasks + tasks on vehicle
		taskList = new Task[nTasks+nCarried];
		tasks.toArray(taskList);
		int i = nTasks;
		for(Task task: vehicle.getCurrentTasks())
			taskList[i++] = task;
		
		initDiameterList();
		mstTable = new HashMap<MSTState, Double>();
		
		// Compute the plan with the selected algorithm.
		switch (algorithm) {
		case NAIVE:
			plan = naivePlan(vehicle, tasks);
			break;
		case ASTAR:
			try {
				plan = astarPlan(vehicle, tasks);
			} catch (Exception e) {
				e.printStackTrace();
			}
			break;
		case BFS:
			try {
				plan = bfsPlan(vehicle, tasks);
			} catch (Exception e) {
				e.printStackTrace();
			}
			break;
		default:
			throw new AssertionError("Should not happen.");
		}
		//priting running time
		System.out.print("Time for computation: ");
		System.out.println(System.currentTimeMillis()-start);
		return plan;
	}
	
	private void initDiameterList() {
		diameterList = new ArrayList<Diameter>();
		ArrayList<Integer> targetCities = new ArrayList<Integer>();
		for (int i = 0; i < nTasks; i++) {
			boolean isPickupDup = false, isDeliverDup = false;
			int pickupCityId = taskList[i].pickupCity.id;
			int deliverCityId = taskList[i].deliveryCity.id;
			for (int j = 0; j < targetCities.size(); j++) {
				if (targetCities.get(j) == pickupCityId)
					isPickupDup = true;
				if (targetCities.get(j) == deliverCityId)
					isDeliverDup = true;
			}
			if (!isPickupDup) 
				targetCities.add(pickupCityId);
			if (!isDeliverDup && pickupCityId != deliverCityId) 
				targetCities.add(deliverCityId);
		}
		for (int i = nTasks; i < taskList.length; ++i) {
			boolean isDeliverDup = false;
			int deliverCityId = taskList[i].deliveryCity.id;
			for (int j = 0; j < targetCities.size(); j++) {
				if (targetCities.get(j) == deliverCityId) {
					isDeliverDup = true;
					break;
				}
			}
			if (!isDeliverDup) 
				targetCities.add(deliverCityId);
		}
		for (int i = 0; i < targetCities.size(); ++i) {
			for (int j = i + 1; j < targetCities.size(); ++j) {
				int x = targetCities.get(i);
				int y = targetCities.get(j);
				Diameter d = new Diameter(x, y, cityList.get(x).distanceTo(cityList.get(y)));
				diameterList.add(d);
			}
		}
		if (!diameterList.isEmpty())
			Collections.sort(diameterList);
	}
	
	private Plan astarPlan(Vehicle vehicle, TaskSet tasks ) throws Exception{
		City currentCity =  vehicle.getCurrentCity();
		Plan plan = new Plan(currentCity);
		//state[0]: agent position
		//state[1 -- nTasks]: TaskState
		
		BitSet taskState = new BitSet(2*(nTasks + nCarried));
		for(int i = nTasks; i < nTasks + nCarried; i++)
			taskState.set(2*i, true);
		initState = (BitSet) taskState.clone();
		goalState = new BitSet(2*(nTasks + nCarried));
		goalState.set(0, 2*(nTasks + nCarried));
		
		HashMap<Node, StateInfo> visited = new HashMap<Node, StateInfo>();
		PriorityQueue<Node> pending = new PriorityQueue<Node>();
		Node initNode = new Node(currentCity.id, taskState, new StateInfo());
		computeFutureCost(initNode);
		pending.add(initNode);
		Node finalStateNode = null;
		
		int c = 0, c2 = 0; // count for loops
		while(!pending.isEmpty()){
			c2++;
			if (finalStateNode != null) {
				break;
			}
			Node curNode = new Node();
			curNode = pending.poll();
			if(goalState.equals(curNode.taskState)){
				if(finalStateNode == null)
					finalStateNode = curNode;
				else if(finalStateNode.stateInfo.cost>curNode.stateInfo.cost) 
					finalStateNode = curNode;
			}
			if(visited.containsKey(curNode)
					&& visited.get(curNode).cost <= curNode.stateInfo.cost){
				continue;
			}
			List<Node> sucs = findAllSuccessors(curNode);
			for (Node suc : sucs) {
				if (!visited.containsKey(suc) 
						|| visited.get(suc).cost > suc.stateInfo.cost)
					pending.add(suc);
			}
			visited.put(curNode, curNode.stateInfo);
			if ((c2 & 131071) == 0) {
				System.out.print("   current cost: " + curNode.stateInfo.cost);
				System.out.println("  loop count: " + c2);
				if (nTasks > 15 && (c2 >> 17) > 10)
					System.gc();
			}
			c++;
		}
		
		
		System.out.println("pending size: " + pending.size());
		System.out.println("visited size: " + visited.size());
		System.out.println("states searched: " + c);
		System.out.println("loops finished: " + c2);
		//System.out.println(mstTable.size());
//		HashMap<Node, StateInfo> test = new HashMap<Node, StateInfo>();
//		for (Node n : pending) {
//			if (!visited.containsKey(n))
//				test.put(n, n.stateInfo);
//		}
//		System.out.println(test.size());
		
		if(finalStateNode == null)
			throw new Exception("Mission impossible!");
		appendAllActions(plan, finalStateNode, visited);
		return plan;
	}
	
	private Plan bfsPlan(Vehicle vehicle, TaskSet tasks) throws Exception{
		City currentCity =  vehicle.getCurrentCity();
		Plan plan = new Plan(currentCity);
		//state[0]: agent position
		//state[1 -- nTasks]: TaskState
		BitSet taskState = new BitSet(2*(nTasks + nCarried));
		for(int i = nTasks; i < nTasks + nCarried; i++)
			taskState.set(2*i, true);
		initState = (BitSet) taskState.clone();
		goalState = new BitSet(2*(nTasks + nCarried));
		goalState.set(0, 2*(nTasks + nCarried));
		
		HashMap<Node,StateInfo> visited = new HashMap<Node, StateInfo>();
		Queue<Node> pending = new LinkedList<Node>();
		Node initNode = new Node(currentCity.id, taskState, new StateInfo());
		initNode.stateInfo.cost = 0.0;
		pending.add(initNode);
		Node finalStateNode = null;
		
		// count for number of loops
		int c = 0, c2 = 0;
		
		while(!pending.isEmpty()){
			c2++;
			Node curNode = pending.remove();
			if(goalState.equals(curNode.taskState)){
				if(finalStateNode == null)
					finalStateNode = curNode;
				else if(finalStateNode.stateInfo.cost>curNode.stateInfo.cost)
					finalStateNode = curNode;
			}
			if(visited.containsKey(curNode) 
					&& visited.get(curNode).cost <= curNode.stateInfo.cost){
				continue;
			}
			List<Node> sucs = findAllSuccessors(curNode);
			for (Node suc : sucs) {
				if (!visited.containsKey(suc) 
						|| visited.get(suc).cost > suc.stateInfo.cost)
					pending.add(suc);
			}
			visited.put(curNode, curNode.stateInfo);
			if ((c2 & 131071) == 0) {
				System.out.println("  loop count: " + c2);
			}
			c++;
		}	
		System.out.println("pending size: " + pending.size());
		System.out.println("states searched: " + c);
		System.out.println("loops finished: " + c2);
		System.out.println("visited size: " + visited.size());
		
		if(finalStateNode == null)
			throw new Exception("Mission impossible!");
		appendAllActions(plan, finalStateNode, visited);
		return plan;
	}
	
	private void computeFutureCost(Node curNode) {
		double futureCost = 0.0;
		MSTState mst = new MSTState();
		for(int i = 0; i < nTasks + nCarried; i++){
			if(!curNode.taskState.get(2*i+1) && !curNode.taskState.get(2*i)){ // 0 0 : WAITING
				mst.isCityAlive[taskList[i].pickupCity.id] = true;
				mst.isCityAlive[taskList[i].deliveryCity.id] = true;
				futureCost = Math.max(futureCost, 
						costPerKm*(taskList[i].pathLength()+
								cityList.get(curNode.curCityId).distanceTo(taskList[i].pickupCity)));
			}else if(!curNode.taskState.get(2*i+1) && curNode.taskState.get(2*i)){ // 0 1 : PICKEDUP
				mst.isCityAlive[taskList[i].deliveryCity.id] = true;
				futureCost = Math.max(futureCost, 
						costPerKm*cityList.get(curNode.curCityId).distanceTo(taskList[i].deliveryCity));
			}
		}
		if (heuristic != Heuristic.BASIC) {
			int diaId = curNode.stateInfo.curDiaId;
			while (diaId < diameterList.size()) {
				if (mst.isCityAlive[diameterList.get(diaId).x] && mst.isCityAlive[diameterList.get(diaId).y]) {
					double diaCost = diameterList.get(diaId).distance
							+ Math.min(cityList.get(diameterList.get(diaId).x).distanceTo(cityList.get(curNode.curCityId)),
									cityList.get(diameterList.get(diaId).y).distanceTo(cityList.get(curNode.curCityId)));
					diaCost = costPerKm * diaCost;
					futureCost = Math.max(futureCost, diaCost);
					break;
				}
				diaId++;
			}
			curNode.stateInfo.curDiaId = diaId;
		}
		
		if (heuristic == Heuristic.MST) {
			mst.isCityAlive[curNode.curCityId] = true;
			futureCost = Math.max(futureCost, costPerKm * computeMSTLength(mst));
		}
		
		//futureCost = 0.0; // uncomment this will be Dijkstra
		curNode.stateInfo.cost += futureCost;
	}
	
	private double computeMSTLength(MSTState mst) {
		if (mstTable.containsKey(mst)) {
			return mstTable.get(mst);
		}
		boolean remainCities[] = new boolean[cityList.size()];
		System.arraycopy(mst.isCityAlive, 0, remainCities, 0, mst.isCityAlive.length);
		int cur = -1;
		double dist[] = new double[mst.isCityAlive.length];
		int nCityAlive = 0;
		double treeLen = 0;
		int next = 0;
		double nextDist = Double.MAX_VALUE;
		for (int i = 0; i < remainCities.length; ++i) {
			if (remainCities[i]) {
				if (cur == -1) {
					cur = i;
					remainCities[i] = false;
				} else {
					nCityAlive++;
					dist[i] = cityList.get(cur).distanceTo(cityList.get(i));
					if (dist[i] < nextDist) {
						nextDist = dist[i];
						next = i;
					}
				}
			}
		}		
		cur = next;
		nCityAlive--;
		while (nCityAlive > 0) {
			remainCities[next] = false;
			nextDist = Double.MAX_VALUE;
			for (int i = 0; i < remainCities.length; i++) {
				if (remainCities[i]) {
					dist[i] = Math.min(dist[i], cityList.get(cur).distanceTo(cityList.get(i)));
					if (dist[i] < nextDist) {
						next = i;
						nextDist = dist[i];
					}
				}
			}
			treeLen += nextDist;
			cur = next;
			nCityAlive--;
		}
		mstTable.put(mst, treeLen);
		return treeLen;
	}
	
	private List<Node> findAllSuccessors(Node curNode){
		List<Node> sucs = new ArrayList<Node>();
		int curLoad = 0;
		BitSet curState = curNode.taskState;
		for(int i = 0; i < nTasks + nCarried; i++)
			if(!curState.get(2*i+1) && curState.get(2*i))	// 0 1 : PICKEDUP -> to compute current load
				curLoad += taskList[i].weight;
		for(int i = 0; i < nTasks + nCarried; i++){
			if(!curState.get(2*i+1) && !curState.get(2*i)	// 0 0 : WAITING 
					&& taskList[i].weight+curLoad <= capacity){ // and remaining capacity is enough
				BitSet newState = (BitSet) curState.clone();
				newState.set(2*i); // set task i as PICKEDUP
				int newCityId = taskList[i].pickupCity.id;
				double pastCost = curNode.stateInfo.pastCost
						+ this.costPerKm* this.cityList.get(curNode.curCityId).distanceTo(taskList[i].pickupCity);
				Node suc = new Node(newCityId, newState, 
						new StateInfo(curNode.curCityId, i, pastCost, pastCost, curNode.stateInfo.curDiaId));
				if (algorithm == Algorithm.ASTAR)
					computeFutureCost(suc);
				sucs.add(suc);
			}else if(!curState.get(2*i+1) && curState.get(2*i)){	// 0 1 : PICKEDUP
				BitSet newState = (BitSet) curState.clone();
				newState.set(2*i + 1); // set task i as DELIVERED
				int newCityId = taskList[i].deliveryCity.id;
				double pastCost = curNode.stateInfo.pastCost 
						+ this.costPerKm* this.cityList.get(curNode.curCityId).distanceTo(taskList[i].deliveryCity);
				Node suc = new Node(newCityId, newState, 
						new StateInfo(curNode.curCityId, i, pastCost, pastCost, curNode.stateInfo.curDiaId));
				if (algorithm == Algorithm.ASTAR)
					computeFutureCost(suc);
				sucs.add(suc);
			}
		}
		return sucs;
	}
	
	//after achieving goal, trace-back all actions and append them to plan
	private void appendAllActions(Plan plan, Node finalStateNode, HashMap<Node, StateInfo>visited){
		//test
		//testPrint(visited);
		
		List<Action> actionList = new ArrayList<Action>();
		BitSet curState = (BitSet) finalStateNode.taskState.clone();
		Node curNode = new Node(finalStateNode.curCityId, curState, finalStateNode.stateInfo);
		while(!initState.equals(curNode.taskState)){
			int idx = curNode.stateInfo.targetTaskIndex;
			City curCity = cityList.get(curNode.curCityId);
			City preCity = cityList.get(curNode.stateInfo.preCityID);
			assert(curState.get(idx*2) || curState.get(idx*2 + 1));
			if(curState.get(idx*2+1) && curState.get(idx*2)){  // if task idx is DELIVERED
				actionList.add(0, new Delivery(taskList[idx]));
				curState.set(idx*2+1, false);
			}
			else {	// task idx is PICKEDUP
				actionList.add(0, new Pickup(taskList[idx]));
				curState.set(idx*2, false);
			}
			if(!preCity.equals(curCity)){
				actionList.add(0, new Move(curCity));
				for(City city: curCity.pathTo(preCity))
					actionList.add(0, new Move(city));
				actionList.remove(0);
			}
			curNode.curCityId = curNode.stateInfo.preCityID;
			curNode.stateInfo = visited.get(curNode);
			if (curNode.stateInfo == null) {
				int aaaa = 0;
			}
		}
		for(Action act : actionList)
			plan.append(act);
	}
	
	//default code provided by TAs==================================
	private Plan naivePlan(Vehicle vehicle, TaskSet tasks) {
		City current = vehicle.getCurrentCity();
		Plan plan = new Plan(current);

		for (Task task : tasks) {
			// move: current city => pickup location
			for (City city : current.pathTo(task.pickupCity))
				plan.appendMove(city);

			plan.appendPickup(task);

			// move: pickup location => delivery location
			for (City city : task.path())
				plan.appendMove(city);

			plan.appendDelivery(task);

			// set current city
			current = task.deliveryCity;
		}
		return plan;
	}

	@Override
	public void planCancelled(TaskSet carriedTasks) {
		if (!carriedTasks.isEmpty()) {
			// This cannot happen for this simple agent, but typically
			// you will need to consider the carriedTasks when the next
			// plan is computed.
		}
	}
	
	private void testPrint(HashMap<Node, StateInfo> visited) {
		for(Map.Entry<Node, StateInfo> entry : visited.entrySet()) {
			  Node key = entry.getKey();
			  StateInfo value = entry.getValue();
			  System.out.print(key.curCityId + " ");
			  for (int i = 0; i < nTasks + nCarried; ++i) {
				  boolean b1 = key.taskState.get(2*i+1);
				  boolean b0 = key.taskState.get(2*i);
				  if (b1 && b0) 
					  System.out.print('D' + " ");
				  else if (!b1 && b0)
					  System.out.print('P' + " ");
				  else if (!b1 && !b0)
					  System.out.print('W' + " ");
				  else 
					  System.out.print("error!");
			  }
			  System.out.print(": " + value.toString());
			  System.out.println();
			}
	}
}
