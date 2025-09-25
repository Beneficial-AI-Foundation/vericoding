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

   // Adds a new vertex v to this graph.
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method addVertex(v: T)
     requires v !in V
     ensures E == old(E) && V == old(V) + {v}
// </vc-spec>
// <vc-code>
{
        V := V + {v};
}
// </vc-code>

// Obtains the set of vertices adjacent to a given vertex v. 
   function getAdj(v: T): set<T>
     requires v in V
     {
        set e | e in E && e.0 == v :: e.1
     } 


}