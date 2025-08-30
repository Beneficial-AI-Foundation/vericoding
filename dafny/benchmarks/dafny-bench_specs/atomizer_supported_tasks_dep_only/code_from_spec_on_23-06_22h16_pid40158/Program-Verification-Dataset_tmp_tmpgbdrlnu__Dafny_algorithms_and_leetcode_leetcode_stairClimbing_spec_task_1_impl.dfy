// ATOM Steps
datatype Steps = One | Two

// ATOM stepSum
function stepSum(xs: seq<Steps>): nat {
    if xs == [] then 0 else (match xs[0] {
        case One => 1
        case Two => 2
    } + stepSum(xs[1..]))
}

// ATOM stepEndsAt
ghost predicate stepEndsAt(xs: seq<Steps>, n: nat) {
    stepSum(xs) == n
}

// ATOM allEndAtN
ghost predicate allEndAtN(ss: set<seq<Steps> >, n: nat) {
    forall xs ::  xs in ss ==> stepEndsAt(xs, n)
}

// ATOM stepBaseZero
lemma stepBaseZero() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 0) && |ss| == 1
{
    var ss := {[]};
    assert stepSum([]) == 0;
    assert stepEndsAt([], 0);
    assert allEndAtN(ss, 0);
}

// ATOM stepBaseOne
lemma stepBaseOne() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 1) && |ss| == 1
{
    var ss := {[One]};
    assert stepSum([One]) == 1;
    assert allEndAtN(ss, 1);
}

// ATOM stepBaseTwo
lemma stepBaseTwo() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 2) && |ss| == 2
{
    var ss := {[One, One], [Two]};
    assert stepSum([One, One]) == 2;
    assert stepSum([Two]) == 2;
    assert allEndAtN(ss, 2);
}

// ATOM plusOne
ghost function plusOne(x: seq<Steps>): seq<Steps> {
    [One]+x
}

// ATOM addOne
ghost function addOne(ss: set<seq<Steps>>): set<seq<Steps>> 
    ensures forall x :: x in ss ==> plusOne(x) in addOne(ss)
    ensures addOne(ss) == set x | x in ss :: plusOne(x)
{
    set x | x in ss :: plusOne(x)
}

// ATOM UnequalSeqs
lemma UnequalSeqs<T>(xs: seq<T>, ys: seq<T>, someT: T)
    requires xs != ys
    ensures [someT]+xs != [someT]+ys
{
    if |xs| != |ys| {
        assert |[someT]+xs| != |[someT]+ys|;
    } else {
        assert |xs| == |ys|;
        var i :| 0 <= i < |xs| && xs[i] != ys[i];
        assert ([someT]+xs)[i+1] != ([someT]+ys)[i+1];
    }
}

// ATOM plusOneNotIn
lemma plusOneNotIn(ss: set<seq<Steps>>, x: seq<Steps>)
    requires x !in ss
    ensures plusOne(x) !in addOne(ss)
{
    if plusOne(x) in addOne(ss) {
        var y :| y in ss && plusOne(y) == plusOne(x);
        UnequalSeqs(x, y, One);
        assert false;
    }
}

// ATOM addOneSize
lemma addOneSize(ss: set<seq<Steps>>)
    ensures |addOne(ss)| == |ss|
{
    if ss == {} {
        assert addOne(ss) == {};
    } else {
        var x :| x in ss;
        var rest := ss - {x};
        addOneSize(rest);
        plusOneNotIn(rest, x);
        assert addOne(ss) == addOne(rest) + {plusOne(x)};
        assert plusOne(x) !in addOne(rest);
        assert |addOne(ss)| == |addOne(rest)| + 1;
        assert |addOne(ss)| == |rest| + 1;
        assert |addOne(ss)| == |ss|;
    }
}

// ATOM plusTwo
ghost function plusTwo(x: seq<Steps>): seq<Steps> {
    [Two]+x
}

// ATOM addTwo
ghost function addTwo(ss: set<seq<Steps>>): set<seq<Steps>> 
    ensures forall x :: x in ss ==> plusTwo(x) in addTwo(ss)
    ensures addTwo(ss) == set x | x in ss :: plusTwo(x)
{
    set x | x in ss :: plusTwo(x)
}

// ATOM plusTwoNotIn
lemma plusTwoNotIn(ss: set<seq<Steps>>, x: seq<Steps>)
    requires x !in ss
    ensures plusTwo(x) !in addTwo(ss)
{
    if plusTwo(x) in addTwo(ss) {
        var y :| y in ss && plusTwo(y) == plusTwo(x);
        UnequalSeqs(x, y, Two);
        assert false;
    }
}

// ATOM addTwoSize
lemma addTwoSize(ss: set<seq<Steps>>)
    ensures |addTwo(ss)| == |ss|
{
    if ss == {} {
        assert addTwo(ss) == {};
    } else {
        var x :| x in ss;
        var rest := ss - {x};
        addTwoSize(rest);
        plusTwoNotIn(rest, x);
        assert addTwo(ss) == addTwo(rest) + {plusTwo(x)};
        assert plusTwo(x) !in addTwo(rest);
        assert |addTwo(ss)| == |addTwo(rest)| + 1;
        assert |addTwo(ss)| == |rest| + 1;
        assert |addTwo(ss)| == |ss|;
    }
}

// ATOM stepSetsAdd
lemma stepSetsAdd(i: nat, steps: array<nat>) 
    requires i >= 2
    requires steps.Length >= i+1
    requires forall k: nat :: k < i ==> exists ss: set< seq<Steps> > :: steps[k] == |ss| && allEndAtN(ss, k)
    ensures exists sp : set< seq<Steps> > :: |sp| == steps[i-1] + steps[i-2] && allEndAtN(sp, i)
{
    var oneStepBack :| steps[i-1] == |oneStepBack| && allEndAtN(oneStepBack, i-1);
    var twoStepBack :| steps[i-2] == |twoStepBack| && allEndAtN(twoStepBack, i-2);
    var stepForward := addOne(oneStepBack);
    var stepTwoForward := addTwo(twoStepBack);
    
    // Prove disjointness
    forall x | x in stepForward
        ensures x !in stepTwoForward
    {
        assert x in stepForward;
        var orig :| orig in oneStepBack && x == plusOne(orig);
        assert stepSum(orig) == i-1;
        assert stepSum(x) == 1 + stepSum(orig) == i;
        assert x[0] == One;
        
        if x in stepTwoForward {
            var orig2 :| orig2 in twoStepBack && x == plusTwo(orig2);
            assert x[0] == Two;
            assert false;
        }
    }
    
    addOneSize(oneStepBack);
    addTwoSize(twoStepBack);
    var sumSet := stepForward + stepTwoForward;
    assert stepForward !! stepTwoForward;
    assert |sumSet| == |stepForward| + |stepTwoForward|;
    assert |sumSet| == steps[i-1] + steps[i-2];
    
    // Prove all elements end at i
    forall x | x in sumSet
        ensures stepEndsAt(x, i)
    {
        if x in stepForward {
            var orig :| orig in oneStepBack && x == plusOne(orig);
            assert stepSum(x) == 1 + stepSum(orig) == 1 + (i-1) == i;
        } else {
            var orig :| orig in twoStepBack && x == plusTwo(orig);
            assert stepSum(x) == 2 + stepSum(orig) == 2 + (i-2) == i;
        }
    }
    
    assert allEndAtN(sumSet, i);
}

// IMPL climbStairs
method climbStairs(n: nat) returns (count: nat) 
    ensures exists ss: set< seq<Steps> > :: count == |ss| && allEndAtN(ss, n)
{
    if n == 0 {
        stepBaseZero();
        count := 1;
        return;
    }
    if n == 1 {
        stepBaseOne();
        count := 1;
        return;
    }
    
    var steps := new nat[n+1];
    steps[0] := 1;
    steps[1] := 1;
    
    /* code modified by LLM (iteration 1): Call base case lemmas to establish invariant preconditions */
    stepBaseZero();
    stepBaseOne();
    
    var i := 2;
    while i <= n
        invariant 2 <= i <= n+1
        invariant steps.Length == n+1
        invariant steps[0] == 1 && steps[1] == 1
        invariant forall k: nat :: k < i ==> exists ss: set< seq<Steps> > :: steps[k] == |ss| && allEndAtN(ss, k)
    {
        /* code modified by LLM (iteration 1): Use stepSetsAdd lemma to compute next value */
        stepSetsAdd(i, steps);
        steps[i] := steps[i-1] + steps[i-2];
        i := i + 1;
    }
    
    count := steps[n];
}