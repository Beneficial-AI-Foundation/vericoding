// <vc-preamble>
// Simple directed graph with vertices of any type T.
class {:autocontracts} Graph<T(==)> {
   var V: set<T>; // vertex-set
   var E: set<(T, T)>; // edge-set

   // Class invariant.
   ghost predicate Valid() {
       // edges must refer to vertices that belong to the vertex-set 
       // and self-loops (edges connecting a vertex to itself) are not allowed 
       forall e :: e in E ==> e.0 in V && e.1 in V && e.0 != e.1
   } 

   // Creates an empty graph.
   constructor ()
     ensures V == {} && E == {}
     {
       V:= {};
       E := {};
     }


   // Obtains the set of vertices adjacent to a given vertex v. 
   function getAdj(v: T): set<T>
     requires v in V
     {
        set e | e in E && e.0 == v :: e.1
     } 


    // Collapses a subset C of vertices to a single vertex v (belonging to C).
    // All vertices in C are removed from the graph, except v.  
    // Edges that connect vertices in C are removed from the graph.  
    // In all other edges, vertices belonging to C are replaced by v.
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method collapseVertices(C: set<T>, v: T)
      requires v in C && C <= V 
      ensures V == old(V) - C + {v}
      ensures E == set e | e in old(E) && (e.0 !in C || e.1 !in C) ::
                          (if e.0 in C then v else e.0, if e.1 in C then v else e.1)
// </vc-spec>
// <vc-code>
{
        V := V - C + {v};
        E := set e | e in E && (e.0 !in C || e.1 !in C) ::
                          (if e.0 in C then v else e.0, if e.1 in C then v else e.1);
}
// </vc-code>

}