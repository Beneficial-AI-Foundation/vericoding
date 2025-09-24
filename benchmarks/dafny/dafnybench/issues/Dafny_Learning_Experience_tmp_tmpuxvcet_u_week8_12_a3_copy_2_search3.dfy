// <vc-preamble>
class TwoStacks<T(0)(==)> 
{
    //abstract state
    ghost var s1 :seq<T>
    ghost var s2 :seq<T>
    ghost const N :nat // maximum size of the stacks
    ghost var Repr : set<object>
    //concrete state
    var data: array<T>
    var n1: nat // number of elements in the stack 1
    var n2: nat // number of elements in the stack 2

    ghost predicate Valid()
        reads this,Repr
        ensures Valid() ==> this in Repr &&  |s1| + |s2| <= N && 0 <= |s1| <= N && 0 <=|s2| <= N
    {
        this in Repr && data in Repr && data.Length == N  
         && 0 <= |s1| + |s2| <= N && 0 <=|s1| <= N && 0 <=|s2| <= N
        &&  (|s1| != 0 ==> forall i:: 0<= i < |s1| ==> s1[i] == data[i]) 
        && (|s2| != 0 ==> forall i:: 0<= i < |s2| ==> s2[i] == data[data.Length-1-i])
       && n1 == |s1| && n2 == |s2|
    }

    constructor (N: nat)
        ensures Valid() && fresh(Repr)
        ensures s1 == s2 == [] && this.N == N
    {
        s1,s2,this.N := [],[],N;
        data := new T[N];
        n1, n2 := 0, 0;
        Repr := {this, data};
    }







    ghost predicate Empty1() 
        requires Valid()
        reads this,Repr
        ensures Empty1() ==> |s1| == 0
        ensures Valid()
    {
        |s1| == 0 && n1 == 0
    }

    ghost predicate Empty2() 
        reads this
        ensures Empty2() ==> |s2| == 0
    {
        |s2| == 0 && n2 == 0
    }
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method search3(Element:T) returns (position:int)
        requires Valid()
        ensures position == -1 || position >= 1
        ensures position >= 1 ==> exists i::0 <=i < |s2| && s2[i] == Element && !Empty2()
      //  ensures position == -1 ==> forall i :: 0 <= i < |s2| ==> s2[i] != Element || Empty2()
        ensures Valid()
// </vc-spec>
// <vc-code>
{
        position := 0;
        var n := 0;

        while n != n2
            decreases |s2| - n
            invariant 0 <= n <= |s2|
            invariant Valid()
            invariant position >= 1 ==> exists i::0 <= i < |s2| && s2[i] == Element
            invariant forall i :: |s2| - 1- n < i < |s2| -1  ==> s2[i] != Element
            invariant forall i :: data.Length-n2 < i < data.Length-n2+n ==> data[i] != Element
        {
            if data[data.Length - n2 + n] == Element 
            {
                position :=  n + 1;

                assert data[data.Length -n2 +n] == s2[n2-1-n];
                assert position >= 1 ==> exists i::0 <= i < |s2| && s2[i] == Element;
                assert forall i:: data.Length - |s2| < i< data.Length-1 ==> data[i] == s2[data.Length-i-1];
                assert forall i:: 0 <= i < |s2| ==> s2[i] == data[data.Length-i-1];
                assert  forall i :: |s2| - 1- n < i < |s2| -1  ==> s2[i] != Element;
                assert  forall i :: data.Length-n2 < i < data.Length-n2+n ==> data[i] != Element;
                return position; 
            }
            n := n + 1;
        }

        position := -1;
        assert position >= 1 ==> exists i::0 <= i < |s2| && s2[i] == Element;
        assert forall i:: data.Length - |s2| < i< data.Length-1 ==> data[i] == s2[data.Length-i-1];
        assert forall i:: 0 <= i < |s2| ==> s2[i] == data[data.Length-i-1];
        assert  forall i :: |s2| - 1- n < i < |s2| -1  ==> s2[i] != Element;
        assert  forall i :: data.Length-n2 < i < data.Length-n2+n ==> data[i] != Element;
}
// </vc-code>

}