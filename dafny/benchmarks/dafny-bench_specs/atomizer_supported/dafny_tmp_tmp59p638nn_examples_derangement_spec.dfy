
// ATOM 

predicate derangement(s: seq<nat>) {
    forall i :: 0 <= i < |s| ==> s[i] != i
}


// ATOM 

predicate permutation(s: seq<nat>) {
    forall i :: 0 <= i < |s| ==> i in s
}


// ATOM 

function multisetRange(n: nat): multiset<nat> {
    multiset(seq(n, i => i))
}


// ATOM 

predicate distinct<A(==)>(s: seq<A>) {
    forall x,y :: x != y && 0 <= x <= y < |s| ==> s[x] != s[y]
}


// SPEC 

method test() {
}


 end(links: seq<nat>)
    requires |links| > 0
    requires permutation(links)
    requires derangement(links)
    requires distinct(links)
{
    assume forall x :: x in links ==> 0 <= x < |links|;
    assume forall x :: x in links ==> multiset(links)[x] ==1;
    // assume multiset(links) == multisetRange(|links|);
    var qAct: nat := links[0];
    var i : nat := 0;
    ghost var oldIndex := 0;
    ghost var indices: multiset<nat> := multiset{0};
    ghost var visited: multiset<nat> := multiset{};

    while qAct != 0
    {
        ghost var oldVisit := visited;
        ghost var oldqAct := qAct;
        ghost var oldOldIndex := oldIndex;
        oldIndex := qAct;
        visited := visited + multiset{qAct};
        indices := indices + multiset{qAct};
            // forall x | x in visited 
            //     ensures exists k :: 0 <= k < |links| && links[k] == x && k in indices
            // {
            //     if x == oldqAct {
            //         // assert links[oldOldIndex] == oldqAct;
            //         // assert exists k :: 0 <= k < |links| && links[k] == x && k in indices;
            //     }else {
            //         // assert x in oldVisit;
            //         // assert exists k :: 0 <= k < |links| && links[k] == x && k in indices;
            //     }
            // }
        //}
        qAct := links[qAct];
        i := i + 1;
    }
}
 end(links: seq<nat>)
    requires |links| > 0
    requires permutation(links)
    requires derangement(links)
    requires distinct(links)
{
    assume forall x :: x in links ==> 0 <= x < |links|;
    assume forall x :: x in links ==> multiset(links)[x] ==1;
    // assume multiset(links) == multisetRange(|links|);
    var qAct: nat := links[0];
    var i : nat := 0;
    ghost var oldIndex := 0;
    ghost var indices: multiset<nat> := multiset{0};
    ghost var visited: multiset<nat> := multiset{};

    while qAct != 0
    {
        ghost var oldVisit := visited;
        ghost var oldqAct := qAct;
        ghost var oldOldIndex := oldIndex;
        oldIndex := qAct;
        visited := visited + multiset{qAct};
        indices := indices + multiset{qAct};
            // forall x | x in visited 
            //     ensures exists k :: 0 <= k < |links| && links[k] == x && k in indices
            // {
            //     if x == oldqAct {
            //         // assert links[oldOldIndex] == oldqAct;
            //         // assert exists k :: 0 <= k < |links| && links[k] == x && k in indices;
            //     }else {
            //         // assert x in oldVisit;
            //         // assert exists k :: 0 <= k < |links| && links[k] == x && k in indices;
            //     }
            // }
        //}
        qAct := links[qAct];
        i := i + 1;
    }
}
