/* Starter code for PERT algorithm (Project 4)
 * @author rbk
 */

// change to your netid
package bxa220020;

// replace sxa173731 with your netid below
import bxa220020.Graph;
import bxa220020.Graph.Vertex;
import bxa220020.Graph.AdjList;
import java.util.List;
import bxa220020.Graph.Edge;
import bxa220020.Graph.GraphAlgorithm;
import bxa220020.Graph.Timer;
import bxa220020.Graph.Factory;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.Scanner;

import org.w3c.dom.Node;

public class PERT extends GraphAlgorithm<PERT.PERTVertex> {
    LinkedList<Vertex> finishList;

    // Status symbols
    // 1 = new
    // 2 = active
    // 3 = finished
    int new_;
    int active_;
    int finished_;

    // Maxmimum Critcal Path
    int maximum_;

    public static class PERTVertex implements Factory {

      // Seen boolean for DFS
      boolean seen;

      // Parent veretex for DFS
      Vertex parent;

      // Status int for DAG
      int status;

      // Earliest and Latest c
      int earliestS;
      int earliestF;
      int latestS;
      int latestF;

      // Duratoin and Slack 
      int duration; 
      int slack; 

      // Constructor Function, make every attribute a default value
      public PERTVertex(Vertex u) {
        this.seen = false;
        this.parent = null;
        this.status = 0;

        this.earliestS = 0;
        this.earliestF = 0;
        this.latestS = 0;
        this.latestF = 0;

        this.duration = 0;
        this.slack = 0;
      }

      public PERTVertex make(Vertex u) { 
        return new PERTVertex(u); 
      }
    }

    // Constructor for PERT is private. Create PERT instances with static method pert().
    private PERT(Graph g) {
		  super(g, new PERTVertex(null));

      this.finishList = null;  

      this.new_ = 1;
      this.active_ = 2;
      this.finished_ = 3;
    }


    // Six setters, Duration, Slack, Earliest and Latest Finish, and Earliest and Latest Start
    public void setDuration(Vertex u, int d) {
      this.get(u).duration = d;
    }
    private void setSlack(Vertex u, int s) {
      this.get(u).slack = s;
    }
    private void setEarliestSta_(Vertex u, int e) {
      this.get(u).earliestS = e;
    }
    private void setEarliestFin_(Vertex u, int e) {
      this.get(u).earliestF = e;
    }
    private void setLatestSta_(Vertex u, int l) {
      this.get(u).latestS = l;
    }    
    private void setLatestFin_(Vertex u, int l) {
      this.get(u).latestF = l;
    }

    // Six getters, Duration, Slack, Earliest and Latest Finish, and Earliest and Latest Start
    private int getDuration(Vertex u) {
      return this.get(u).duration;
    }
    private int getSlack(Vertex u) {
      return this.get(u).slack;
    }
    private int getEarliestSta_(Vertex u) {
      return this.get(u).earliestS;
    }
    private int getEarliestFin_(Vertex u) {
      return this.get(u).earliestF;
    }
    private int getLatestSta_(Vertex u) {
      return this.get(u).latestS;
    }    
    private int getLatestFin_(Vertex u) {
      return this.get(u).latestF;
    }

    // Methods to get Earliest and Latest Start and Finish for P4Drivers file
    public int ec(Vertex u) {
      return getEarliestFin_(u);
    }
    public int es(Vertex u) {
      return getEarliestSta_(u);
    }
    public int lc(Vertex u) {
      return getLatestFin_(u);
    }
    public int ls(Vertex u) {
      return getLatestSta_(u);
    }
    public int slack(Vertex u) {
      return getSlack(u);
    }


    // PERT AND TOPOLOGY FUNCTIONS
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////
    // Implement the PERT algorithm. Returns false if the graph g is not a DAG.
    public boolean pert() {

      // Begin pert by checking if graph is DAG and return result to "check_success"
      LinkedList<Vertex> check_success = topologicalOrder();

      // Return boolean variable when pert has is or is not created
      boolean pert_success = false;

      // If "check_success" is null, then graph is not cycle, so return false
      if(check_success != null){
        // Else, convert LinkList to ArrayList
        ArrayList<Vertex> top_order = new ArrayList<>(check_success);

        // Now, set every vertex EarlyStart to 0
        for(Vertex u : top_order){
          setEarliestSta_(u, 0);
        }

        // Loop trough ArrayList
        for(Vertex u : top_order){

          // Set every Vertex EarlyFinish to vertex (EarlyStart + Duration)
          setEarliestFin_(u, getEarliestSta_(u) + getDuration(u));

          // Loop again and get Edges of Vertex
          for(Edge e : g.incident(u)){
            // Get vertex of the other end of current vertex
            Vertex v = e.otherEnd(u);

            // If other vertex Early Start is less than current vertex Early Finish
            // then assing other vertex Early Start with current vertex Early Finish
            if(getEarliestSta_(v) < getEarliestFin_(u)){
              setEarliestSta_(v, getEarliestFin_(u));
            }
          }
        }
        // Now, get maximum CPL of vertexs
        int maxtimer = 0;

        // Loop trough "top_order" and if "maxtimer" is less than current 
        // vertex Early Finish then assign it to "maxtimer"
        for(Vertex u : top_order){
          if(maxtimer < getEarliestFin_(u)){
            maxtimer = getEarliestFin_(u);
          }
        }
        // Once we loop trough every Vertex, assign "maxtimer" to "maximum_" 
        this.maximum_ = maxtimer;

        // Assign "maxtimer" to every vertex Latest Finish
        for(Vertex v : g){
          setLatestFin_(v, maxtimer);
        }
        
        // Reverese "top_order" list
        Collections.reverse(top_order);

        // Loop trough reverse list "top_order"
        for(Vertex u : top_order){
          // Assign current vertex Latest Start with 
          // current vertex (Latest Finish - Duratiom)
          setLatestSta_(u, (getLatestFin_(u) - getDuration(u)));

          // Assign current vertex Slack current vertex (Latest Finish - Earliest Finish)
          setSlack(u, (getLatestFin_(u) - getEarliestFin_(u)));
          
          // Loop trough each edge for current vertex
          for(Edge e : g.inEdges(u)){
            // Get other vertex from edge
            Vertex v = e.otherEnd(u);

            // If other vertex Latest Finish > curretn vertex Latest Start
            if(getLatestFin_(v) > getLatestSta_(u)){
              // Set other vertex Latest Finish to current vertex Latest Start
              setLatestFin_(v, getLatestSta_(u));
            }
          }
        }
        // Set "pert_success" to true since pert has been completed
        pert_success = true;
      }
      // Return "pert_success"
		  return pert_success;
    }

    ////////////////////////////////////////
    // Find a topological order of g using DFS
    LinkedList<Vertex> topologicalOrder() {

      // First if graph is DAG
      boolean check_if_dag = checkDAG();
    
      // If DAG is not false, begin DFS
      if (check_if_dag == true){

        // When dag is true, then begin topology, also, "finishList" is a global variable
        this.finishList = new LinkedList<>();
        dfsALL();
      }

      // Return LinkList of Vertexs
      return this.finishList;
    }

    ////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



    // HELPER FUNCTIONS TOPOLOGY
    ////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////
    // chechDAG() checks if there is no cycles in graph
    boolean checkDAG(){

      // Loop trought each Vertex and give it a status, set it to new
      for(Vertex v : g){
        this.get(v).status = this.new_;
      }
      // Loop vertexs and begin "isDAG()" 
      for(Vertex v : g){

        // If status of vertex is new, go to "isDAG()" to being recursion
        if (this.get(v).status == this.new_){
          if(!isDag(v)){
            
            // Return false if there is cycles
            return false;
          }
        }
      }
      // Return true if no cycles
      return true;
    }

    ////////////////////////////////////////
    // isDAG() function is where it will check for cycles
    boolean isDag(Vertex v){

      // For every new vertex, set it to active
      this.get(v).status = this.active_;

      // Get the list of edges that vertex connects to
      // From the current Vertex to other vertex in the list
      List<Edge> connections = g.adj(v).outEdges;

      //Loop trough every edge and check other Vertex
      for (int i = 0; i < connections.size(); i++){

        // If other vertex is actice, then return false
        if(get(connections.get(i).to).status == this.active_){
          return false;
        }
        // If other vertex is new, go here
        else if (get(connections.get(i).to).status == this.new_){

          // Recurse to "isDag()" and check other vertex edges 
          if (!isDag(connections.get(i).to)){

            // If there is cycle, return false
            return false;
          }
        }
      } 
      // If vertex did not ecounter any cycles, then 
      // set vertex to finish and return true
      this.get(v).status = finished_;
      return true;
    }

    ////////////////////////////////////////
    // dfsALL goes trough graph and stacks vertexs in 
    // topology order using Depth First Search
    void dfsALL(){

      // Loop trough each vertex and set seen to false
      for (Vertex v : g){
        get(v).seen = false;
      }

      // Loop again and begin dfs with first seen false vertex
      for (Vertex v : g){
        if (get(v).seen == false){
          dfs(v);
        }
      }
    }

    ////////////////////////////////////////
    // dfs() function, add vertexs to LinkList "finishList" in topology order
    void dfs(Vertex v){

      // Once vertex has visited here, set seen to true
      get(v).seen = true;

      // Collecting every edge for current vertex
      List<Edge> demo = g.adj(v).outEdges;

      // Loop trought each edge
      for (int i = 0; i < demo.size(); i++){

        // If vertex "to" is seen false, then set its parent to
        //  current vertex and recurse dfs with "to" vertex
        if(get(demo.get(i).to).seen == false){
          get(demo.get(i).to).parent = v;
          dfs(demo.get(i).to);
        }
      }
      // Once edge of vertex is completed, add vertex to LinkList "finishList"
      this.finishList.addFirst(v);
    }

    ////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////



    // CRITICAL FUNCTIONS FOR PATH, CRITICAL, AND NUMCRITICAL
    ///////////////////////////////////////////////////////////////////
    ////////////////////////////////////////
    // Length of a critical path (time taken to complete project)
    public int criticalPath() {
		  return this.maximum_;

    }

    ////////////////////////////////////////
    // Is u a critical vertex?
    public boolean critical(Vertex u) {
      // Create a boolean variable and check 
      // vertex slack if 0 then return 0
      boolean critical_check = false;
      if(get(u).slack == 0){
        critical_check = true;
      }
      return critical_check;
    }

    ////////////////////////////////////////
    // Number of critical vertices in g
    public int numCritical() {
      // Create a variable to count total critial vertices
      int total_critial = 0;

      // Go trought each vertice
      for(Vertex v : g){
        // If the vertice.slack is 0, then increment "total_critial"
        if(get(v).slack == 0){
          total_critial++;
        }
      }
      //Return results
      return total_critial;
    }
    
    ////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////
    

    //OVERALL MAIN FUNCTION 
    /////////////////////////////////////////////////////////
    // Create a PERT instance on g, runs the algorithm.
    // Returns PERT instance if successful. Returns null if G is not a DAG.
    public static PERT pert(Graph g, int[] duration) {

      // Create PERT object
      PERT p = new PERT(g);
      
      // loop trought graph and assign distance to each vertex
      for(Vertex u: g) {
        p.setDuration(u, duration[u.getIndex()]);
      }
      
      // Run PERT algorithm.  Returns false if g is not a DAG
      if(p.pert() == true) {
        return p;
      } else {
        return null;
      }
    }
}
