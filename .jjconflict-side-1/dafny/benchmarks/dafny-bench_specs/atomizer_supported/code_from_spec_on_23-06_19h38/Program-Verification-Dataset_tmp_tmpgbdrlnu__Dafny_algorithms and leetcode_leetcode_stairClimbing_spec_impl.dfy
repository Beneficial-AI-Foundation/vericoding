//IMPL climbStairs
/* code modified by LLM (iteration 4): Added missing type definitions and helper predicates */
datatype Steps = One | Two

predicate allEndAtN(ss: set<seq<Steps>>, n: nat)
{
    forall s :: s in ss ==> |s| > 0 && sumSteps(s) == n
}

function sumSteps(s: seq<Steps>): nat
{
    if |s| == 0 then 0
    else (if s[0] == One then 1 else 2) + sumSteps(s[1..])
}

/* code modified by LLM (iteration 4): Corrected Fibonacci function for climbing stairs */
function fib(n: nat): nat
{
    if n == 0 then 1  // Changed: 1 way to stay at 0 (empty sequence)
    else if n == 1 then 1
    else if n == 2 then 2
    else fib(n-1) + fib(n-2)
}

/* code modified by LLM (iteration 4): Helper lemma for base cases */
lemma stepBaseZero()
    ensures exists ss: set<seq<Steps>> :: 1 == |ss| && (forall s :: s in ss ==> |s| == 0 && sumSteps(s) == 0)
{
    var ss: set<seq<Steps>> := {[]};
    assert [] in ss;
    assert sumSteps([]) == 0;
    assert |ss| == 1;
}

lemma stepBaseOne()
    ensures exists ss: set<seq<Steps>> :: 1 == |ss| && allEndAtN(ss, 1)
{
    var ss: set<seq<Steps>> := {[One]};
    assert [One] in ss;
    assert sumSteps([One]) == 1;
    assert |[One]| == 1 > 0;
    assert allEndAtN(ss, 1);
    assert |ss| == 1;
}

lemma stepBaseTwo()
    ensures exists ss: set<seq<Steps>> :: 2 == |ss| && allEndAtN(ss, 2)
{
    var ss: set<seq<Steps>> := {[One, One], [Two]};
    assert [One, One] in ss && [Two] in ss;
    assert sumSteps([One, One]) == 2;
    assert sumSteps([Two]) == 2;
    assert |[One, One]| > 0 && |[Two]| > 0;
    assert allEndAtN(ss, 2);
    assert |ss| == 2;
}

/* code modified by LLM (iteration 4): Simplified constructive approach */
function constructValidStepSet(n: nat): set<seq<Steps>>
    ensures n == 0 ==> |constructValidStepSet(n)| == 1
    ensures n == 1 ==> |constructValidStepSet(n)| == 1
    ensures n == 2 ==> |constructValidStepSet(n)| == 2
    ensures n >= 3 ==> |constructValidStepSet(n)| == fib(n)
    ensures n == 0 ==> (forall s :: s in constructValidStepSet(n) ==> |s| == 0 && sumSteps(s) == 0)
    ensures n > 0 ==> allEndAtN(constructValidStepSet(n), n)
    decreases n
{
    if n == 0 then {[]}
    else if n == 1 then {[One]}
    else if n == 2 then {[One, One], [Two]}
    else
        var prevSet1 := constructValidStepSet(n-1);
        var prevSet2 := constructValidStepSet(n-2);
        var extended1 := set s | s in prevSet1 :: s + [One];
        var extended2 := set s | s in prevSet2 :: s + [Two];
        extended1 + extended2
}

/* code modified by LLM (iteration 4): Lemma to verify the recursive construction works */
lemma constructValidStepSetCorrect(n: nat)
    ensures var ss := constructValidStepSet(n);
            if n == 0 then |ss| == 1 && (forall s :: s in ss ==> |s| == 0 && sumSteps(s) == 0)
            else |ss| == fib(n) && allEndAtN(ss, n)
    decreases n
{
    var ss := constructValidStepSet(n);
    if n == 0 {
        assert ss == {[]};
        assert |ss| == 1;
        assert forall s :: s in ss ==> |s| == 0 && sumSteps(s) == 0;
    } else if n == 1 {
        assert ss == {[One]};
        assert |ss| == 1;
        assert fib(1) == 1;
        assert allEndAtN(ss, 1);
    } else if n == 2 {
        assert ss == {[One, One], [Two]};
        assert |ss| == 2;
        assert fib(2) == 2;
        assert allEndAtN(ss, 2);
    } else {
        constructValidStepSetCorrect(n-1);
        constructValidStepSetCorrect(n-2);
        
        var prevSet1 := constructValidStepSet(n-1);
        var prevSet2 := constructValidStepSet(n-2);
        var extended1 := set s | s in prevSet1 :: s + [One];
        var extended2 := set s | s in prevSet2 :: s + [Two];
        
        assert |prevSet1| == fib(n-1);
        assert |prevSet2| == fib(n-2);
        assert ss == extended1 + extended2;
        assert |ss| == fib(n-1) + fib(n-2);
        assert fib(n) == fib(n-1) + fib(n-2);
        assert |ss| == fib(n);
        assert allEndAtN(ss, n);
    }
}

method climbStairs(n: nat) returns (count: nat) 
    ensures exists ss: set< seq<Steps> > :: count == |ss| && 
            (if n == 0 then (forall s :: s in ss ==> |s| == 0 && sumSteps(s) == 0) 
             else allEndAtN(ss, n))
{
    if n == 0 {
        stepBaseZero();
        count := 1;  // Changed: 1 way to have 0 steps
        return;
    }
    
    if n == 1 {
        stepBaseOne();
        count := 1;
        return;
    }
    
    if n == 2 {
        stepBaseTwo();
        count := 2;
        return;
    }
    
    // For n >= 3, use dynamic programming approach
    var steps := new nat[n+1];
    steps[0] := 1;  // Changed: 1 way to have 0 steps
    steps[1] := 1;
    steps[2] := 2;
    
    /* code modified by LLM (iteration 4): Corrected loop with proper invariants */
    var i := 3;
    while i <= n
        invariant 3 <= i <= n+1
        invariant steps.Length == n+1
        invariant steps[0] == 1 && steps[1] == 1 && steps[2] == 2
        invariant forall k: nat :: 0 <= k < i ==> steps[k] == fib(k)
        invariant forall k: nat :: 3 <= k < i ==> steps[k] == steps[k-1] + steps[k-2]
    {
        steps[i] := steps[i-1] + steps[i-2];
        
        /* code modified by LLM (iteration 4): Assert the Fibonacci relationship holds */
        assert steps[i] == steps[i-1] + steps[i-2];
        assert steps[i-1] == fib(i-1);
        assert steps[i-2] == fib(i-2);
        assert fib(i) == fib(i-1) + fib(i-2);
        assert steps[i] == fib(i);
        
        i := i + 1;
    }
    
    count := steps[n];
    
    /* code modified by LLM (iteration 4): Final verification using construction */
    assert count == fib(n);
    constructValidStepSetCorrect(n);
    var finalSS := constructValidStepSet(n);
    assert |finalSS| == fib(n);
    assert count == |finalSS|;
    assert allEndAtN(finalSS, n);
}

//IMPL Test
method Test() {
}