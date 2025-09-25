// <vc-preamble>
module IntegerSet {

    class Set {

        var elements: seq<int>;

        constructor Set0() 
        ensures this.elements == []
        ensures |this.elements| == 0
        {
            this.elements := [];
        }

        constructor Set(elements: seq<int>)
        requires forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        ensures this.elements == elements
        ensures forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements|  && j != i:: this.elements[i] != this.elements[j]
        {
            this.elements := elements;
        }





        //for computing the length of the intersection of 2 sets
        function intersect_length(s1 : seq<int>, s2 : seq<int>, count : int, start : int, stop : int) : int 
        requires 0 <= start <= stop
        requires stop <= |s1|
        decreases stop - start
        {
            if start == stop then count else (if s1[start] in s2 then intersect_length(s1, s2, count + 1, start + 1, stop) else intersect_length(s1, s2, count, start + 1, stop))
        }

        //for computing the length of the union of 2 sets
        //pass in the length of s2 as the initial count
        function union_length(s1 : seq<int>, s2 : seq<int>, count : int, i : int, stop : int) : int 
        requires 0 <= i <= stop
        requires stop <= |s1|
        decreases stop - i
        {
            if i == stop then count else (if s1[i] !in s2 then union_length(s1, s2, count + 1, i + 1, stop) else union_length(s1, s2, count, i + 1, stop))
        }
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method union(s : Set) returns (union : Set)
        requires forall i, j | 0 <= i < |s.elements| && 0 <= j < |s.elements| && i != j :: s.elements[i] != s.elements[j]
        requires forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements| && i != j :: this.elements[i] != this.elements[j]
        ensures forall i : int :: i in s.elements || i in this.elements <==> i in union.elements
        ensures forall i : int :: i !in s.elements && i !in this.elements <==> i !in union.elements
        ensures forall j, k | 0 <= j < |union.elements| && 0 <= k < |union.elements| && j != k :: union.elements[j] != union.elements[k]
        ensures fresh(union)
// </vc-spec>
// <vc-code>
{
            var elems := s.elements;
            union := new Set.Set0();

            var i := 0;
            while (0 <= i < |this.elements|)
            decreases |this.elements| - i
            invariant 0 <= i < |this.elements| || i == 0
            invariant forall j : int :: 0 <= j < |s.elements| ==> s.elements[j] in elems
            invariant forall j : int :: 0 <= j < i < |this.elements| ==> (this.elements[j] in elems <==> (this.elements[j] in s.elements || this.elements[j] in this.elements))
            invariant forall j :: 0 <= j < |elems| ==> elems[j] in this.elements || elems[j] in s.elements
            invariant forall j, k :: 0 <= j < |elems| && 0 <= k < |elems| && j != k ==> elems[j] != elems[k]
            {
                if (this.elements[i] !in elems) {
                    elems := elems + [this.elements[i]];
                }
                if (i == |this.elements| - 1) {
                    break;
                }
                i := i + 1;
            }

            union.elements := elems;
}
// </vc-code>

}
}