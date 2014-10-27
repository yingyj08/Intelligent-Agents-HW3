package template;

/* import table */
import java.util.ArrayList;
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
	
	/* */
	/* class for search algorithms */
	class Node implements Comparable<Node>{
		private int[] state;
		private StateInfo stateInfo;
		private Node(){stateInfo = new StateInfo();}
		private Node(int[] state, StateInfo stateInfo){
			this.state = state;
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
		    for (int i = 0; i < this.state.length; ++i) {
		    	if (this.state[i] != otherNode.state[i])
		    		return false;
		    }
			return true;
		}
		@Override
		public int hashCode() {
			//JSHash
            int hash = 1315423911;
            for (int i = 0; i < state.length; i++) {
                    hash ^= ((hash << 5) + state[i] + (hash >> 2));
            }

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
		Plan plan = null;
		nCarried = vehicle.getCurrentTasks().size(); //update the #carried tasks
		nTasks = tasks.size();//update #left-over tasks
		taskList = new Task[nTasks+nCarried];
		tasks.toArray(taskList);
		int i = nTasks;
		for(Task task: vehicle.getCurrentTasks())
			taskList[i++] = task;
		initDiameterList();
		
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
		City current =  vehicle.getCurrentCity();
		Plan plan = new Plan(current);
		//state[0]: agent position
		//state[1 -- nTasks]: TaskState
		int[]  state = new int[nTasks+1+nCarried];
		state[0] = current.id;
		for(int i = 1; i <= nTasks; i++)
			state[i] = WAITING;
		for(int i = nTasks+1; i < state.length; i++)
			state[i] = PICKEDUP;
		
		HashMap<Node, StateInfo> visited = new HashMap<Node, StateInfo>();
		PriorityQueue<Node> pending = new PriorityQueue<Node>();
		Node initNode = new Node(state, new StateInfo());
		computeFutureCost(initNode);
		pending.add(initNode);
		Node finalStateNode = null;
		
		//TODO test
		int c = 0, c2 = 0;
		
		while(!pending.isEmpty()){
			c2++;
			if (finalStateNode != null) {
				break;
			}
			Node curNode = new Node();
			curNode = pending.poll();
			if(isGoalState(curNode.state)){
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
			//System.out.println(curNode.stateInfo.cost + " " + c + " " + pending.size());
			c++;
		}
		
		System.out.println(c);
		System.out.println(c2);
		System.out.println(pending.size());
		System.out.println(visited.size());
		
		if(finalStateNode == null)
			throw new Exception("Mission impossible!");
		appendAllActions(plan, finalStateNode, visited);
		return plan;
	}
	
	private Plan bfsPlan(Vehicle vehicle, TaskSet tasks) throws Exception{
		City current =  vehicle.getCurrentCity();
		Plan plan = new Plan(current);
		//state[0]: agent position
		//state[1 -- nTasks]: TaskState
		int[]  state = new int[nTasks+1+nCarried];
		state[0] = current.id;
		for(int i = 1; i <= nTasks; i++)
			state[i] = WAITING;
		for(int i = nTasks+1; i < state.length; i++)
			state[i] = PICKEDUP;
		
		HashMap<Node,StateInfo> visited = new HashMap<Node, StateInfo>();
		Queue<Node> pending = new LinkedList<Node>();
		Node initNode = new Node(state, new StateInfo());
		initNode.stateInfo.cost = 0.0;
		pending.add(initNode);
		Node finalStateNode = null;
		
		//TODO test
		int c = 0, c2 = 0;
		
		while(!pending.isEmpty()){
			c2++;
			Node curNode = pending.remove();
			if(isGoalState(curNode.state)){
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
			c++;
		}	
		System.out.println(c);
		System.out.println(c2);
		System.out.println(pending.size());
		System.out.println(visited.size());
		
		if(finalStateNode == null)
			throw new Exception("Mission impossible!");
		appendAllActions(plan, finalStateNode, visited);
		return plan;
	}
	
	private void computeFutureCost(Node curNode) {
		double futureCost = 0.0;
		boolean isCityAlive[] = new boolean[cityList.size()];
		for(int i = 1; i < curNode.state.length; i++){
			if(curNode.state[i] == WAITING){
				isCityAlive[taskList[i-1].pickupCity.id] = true;
				isCityAlive[taskList[i-1].deliveryCity.id] = true;
				futureCost = Math.max(futureCost, 
						costPerKm*(taskList[i-1].pathLength()+
								cityList.get(curNode.state[0]).distanceTo(taskList[i-1].pickupCity)));
			}else if(curNode.state[i] == PICKEDUP){
				isCityAlive[taskList[i-1].deliveryCity.id] = true;
				futureCost = Math.max(futureCost, 
						costPerKm*cityList.get(curNode.state[0]).distanceTo(taskList[i-1].deliveryCity));
			}
		}
		if (heuristic != Heuristic.BASIC) {
			int diaId = curNode.stateInfo.curDiaId;
			while (diaId < diameterList.size()) {
				if (isCityAlive[diameterList.get(diaId).x] && isCityAlive[diameterList.get(diaId).y]) {
					double diaCost = diameterList.get(diaId).distance
							+ Math.min(cityList.get(diameterList.get(diaId).x).distanceTo(cityList.get(curNode.state[0])),
									cityList.get(diameterList.get(diaId).y).distanceTo(cityList.get(curNode.state[0])));
					diaCost = costPerKm * diaCost;
					futureCost = Math.max(futureCost, diaCost);
					break;
				}
				diaId++;
			}
			curNode.stateInfo.curDiaId = diaId;
		}
		
		if (heuristic == Heuristic.MST) {
			isCityAlive[curNode.state[0]] = true;
			futureCost = Math.max(futureCost, costPerKm * computeMSTLength(isCityAlive));
		}
		
		//futureCost = 0.0; // uncomment this will be Dijkstra
		curNode.stateInfo.cost += futureCost;
	}
	
	private double computeMSTLength(boolean[] isCityAlive) {
		int cur = -1;
		double dist[] = new double[isCityAlive.length];
		int nCityAlive = 0;
		double treeLen = 0;
		int next = 0;
		double nextDist = Double.MAX_VALUE;
		for (int i = 0; i < isCityAlive.length; ++i) {
			if (isCityAlive[i]) {
				if (cur == -1) {
					cur = i;
					isCityAlive[i] = false;
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
			isCityAlive[next] = false;
			nextDist = Double.MAX_VALUE;
			for (int i = 0; i < isCityAlive.length; i++) {
				if (isCityAlive[i]) {
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
		return treeLen;
	}
	
	private List<Node> findAllSuccessors(Node curNode){
		List<Node> sucs = new ArrayList<Node>();
		int curLoad = 0;
		int[] curState = curNode.state;
		for(int i = 1; i < curState.length; i++)
			if(curState[i] == PICKEDUP)
				curLoad += taskList[i-1].weight;
		for(int i = 1; i < curState.length; i++){
			if(curState[i] == WAITING && taskList[i-1].weight+curLoad <= capacity){
				int[] newState = new int[curState.length];
				System.arraycopy(curState, 0, newState, 0, curState.length);
				newState[i] = PICKEDUP;
				newState[0] = taskList[i-1].pickupCity.id;
				double pastCost = curNode.stateInfo.pastCost
						+ this.costPerKm* this.cityList.get(curState[0]).distanceTo(taskList[i-1].pickupCity);
				Node suc = new Node(newState, 
						new StateInfo(curState[0], i, pastCost, pastCost, curNode.stateInfo.curDiaId));
				if (algorithm == Algorithm.ASTAR)
					computeFutureCost(suc);
				sucs.add(suc);
			}else if(curState[i] == PICKEDUP){
				int[] newState = new int[curState.length];
				System.arraycopy(curState, 0, newState, 0, curState.length);
				newState[i] = DELIVERED;
				newState[0] = taskList[i-1].deliveryCity.id;
				double pastCost = curNode.stateInfo.pastCost 
						+ this.costPerKm* this.cityList.get(curState[0]).distanceTo(taskList[i-1].deliveryCity);
				Node suc = new Node(newState, 
						new StateInfo(curState[0], i, pastCost, pastCost, curNode.stateInfo.curDiaId));
				if (algorithm == Algorithm.ASTAR)
					computeFutureCost(suc);
				sucs.add(suc);
			}
		}
		return sucs;
	}
	
	private void appendAllActions(Plan plan, Node finalStateNode, HashMap<Node, StateInfo>visited){
		List<Action> actionList = new ArrayList<Action>();
		int[] curState = new int[finalStateNode.state.length];
		System.arraycopy(finalStateNode.state, 0, curState, 0, curState.length);
		Node curNode = new Node(curState, finalStateNode.stateInfo);
		while(!isInitState(curNode.state)){
			int idx = curNode.stateInfo.targetTaskIndex;
			City curCity = cityList.get(curState[0]);
			City preCity = cityList.get(curNode.stateInfo.preCityID);
			assert(curState[idx]>0);
			if(curState[idx] == DELIVERED)
				actionList.add(0, new Delivery(taskList[idx-1]));
			else
				actionList.add(0, new Pickup(taskList[idx-1]));
			curState[idx]--;
			if(!preCity.equals(curCity)){
				actionList.add(0, new Move(curCity));
				for(City city: curCity.pathTo(preCity))
					actionList.add(0, new Move(city));
				actionList.remove(0);
			}
			curState[0] = curNode.stateInfo.preCityID;
			curNode.stateInfo = visited.get(curNode);
		}
		for(Action act : actionList)
			plan.append(act);
	}
	
	private boolean isInitState(int[] state){
		for(int i = 1; i <= nTasks; i++)
			if(state[i] != WAITING)
				return false;
		for(int i = 0; i < nCarried; i++)
			if(state[i+nTasks+1]!=PICKEDUP)
				return false;
		return true;
	}
	private boolean isGoalState(int[] state){
		for(int i = 1; i < state.length; i++)
			if(state[i] != DELIVERED)
				return false;
		return true;
	}
	
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
}
