/*
You are climbing a staircase. It takes n steps to reach the top.

Each time you can either climb 1 or 2 steps. In how many distinct ways can you climb to the top?
// SPEC 

method climbStairs(n: nat) returns (count: nat) 
    ensures exists ss: set< seq<Steps> > :: count == |ss| && allEndAtN(ss, n)
{
}
;
*/

//ATOM_PLACEHOLDER_Steps// ATOM 

function stepSum(xs: seq<Steps>): nat {
    if xs == [] then 0 else (match xs[0] {
        case One => 1
        case Two => 2
    } + stepSum(xs[1..]))
}


// ATOM 

ghost predicate stepEndsAt(xs: seq<Steps>, n: nat) {
    stepSum(xs) == n
}

// ATOM 
ghost predicate allEndAtN(ss: set<seq<Steps> >, n: nat) {
    forall xs ::  xs in ss ==> stepEndsAt(xs, n)
}


// ATOM 

lemma stepBaseZero() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 0) && |ss| == 0
{
}

// ATOM 
lemma stepBaseOne() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 1) && |ss| == 1
{
}


// ATOM 

lemma stepBaseTwo() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 2) && |ss| == 2
{
}


// ATOM 

ghost function plusOne(x: seq<Steps>): seq<Steps> {
    [One]+x
}


// ATOM 

ghost function addOne(ss: set<seq<Steps>>): set<seq<Steps>> 
    ensures forall x :: x in ss ==> plusOne(x) in addOne(ss)
    ensures addOne(ss) == set x | x in ss :: plusOne(x)
{
    set x | x in ss :: plusOne(x)
}


//ATOM_PLACEHOLDER_SeqsNotEqualImplication

// ATOM 

lemma UnequalSeqs<T>(xs: seq<T>, ys: seq<T>, someT: T)
    requires xs != ys
    ensures [someT]+xs != [someT]+ys
{
    if |xs| < |ys| {} else if |ys| > |xs| {}
    else if i: nat :| i < |xs| && i <|ys| && xs[i] != ys[i] {
    }
}


// ATOM 

lemma plusOneNotIn(ss: set<seq<Steps>>, x: seq<Steps>)
    requires x !in ss
    ensures plusOne(x) !in addOne(ss)
{
    if x == [] {
    }
    if plusOne(x) in addOne(ss) {
        forall y | y in ss 
            ensures y != x
            ensures plusOne(y) in addOne(ss)
            ensures plusOne(y) != plusOne(x)
        {
            UnequalSeqs(x, y, One);
        }
    }
}


// ATOM 

lemma addOneSize(ss: set<seq<Steps>>)
    ensures |addOne(ss)| == |ss|
{
    var size := |ss|;
    if x :| x in ss {
        addOneSize(ss - {x});
        plusOneNotIn(ss-{x}, x);
    }else{

    }
}


// ATOM 

ghost function addOne(ss: set<seq<Steps>>): set<seq<Steps>> 
    ensures forall x :: x in ss ==> plusOne(x) in addOne(ss)
    ensures addOne(ss) == set x | x in ss :: plusOne(x)
{
    set x | x in ss :: plusOne(x)
}
Sum

//ATOM_PLACEHOLDER_endAtNPlus

// ATOM 

ghost function plusTwo(x: seq<Steps>): seq<Steps> {
    [Two]+x
}


// ATOM 

ghost function addTwo(ss: set<seq<Steps>>): set<seq<Steps>> 
    ensures forall x :: x in ss ==> plusTwo(x) in addTwo(ss)
    ensures addTwo(ss) == set x | x in ss :: plusTwo(x)
{
    set x | x in ss :: plusTwo(x)
}


// ATOM 

lemma plusTwoNotIn(ss: set<seq<Steps>>, x: seq<Steps>)
    requires x !in ss
    ensures plusTwo(x) !in addTwo(ss)
{
    if x == [] {
    }
    if plusTwo(x) in addTwo(ss) {
        forall y | y in ss 
            ensures y != x
            ensures plusTwo(y) in addTwo(ss)
            ensures plusTwo(y) != plusTwo(x)
        {
            UnequalSeqs(x, y, Two);
        }
    }
}


// ATOM 

lemma addTwoSize(ss: set<seq<Steps>>)
    ensures |addTwo(ss)| == |ss|
{
    var size := |ss|;
    if x :| x in ss {
        // assert |ss - {x}| == size - 1;
        addTwoSize(ss - {x});
        // assert |addTwo(ss-{x})| == size - 1;
        // assert x !in ss-{x};
        plusTwoNotIn(ss-{x}, x);
        // assert plusTwo(x) !in addTwo(ss-{x});
    }
}


// ATOM 

ghost function addTwo(ss: set<seq<Steps>>): set<seq<Steps>> 
    ensures forall x :: x in ss ==> plusTwo(x) in addTwo(ss)
    ensures addTwo(ss) == set x | x in ss :: plusTwo(x)
{
    set x | x in ss :: plusTwo(x)
}
Sum

//ATOM_PLACEHOLDER_setSizeAddition

// ATOM 

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
    // assert stepForward !! stepTwoForward;
    addOneSize(oneStepBack);
    addTwoSize(twoStepBack);
    var sumSet := stepForward + stepTwoForward;
    // assert |sumSet| == steps[i-1]+steps[i-2];
}


// SPEC 

method climbStairs(n: nat) returns (count: nat) 
    ensures exists ss: set< seq<Steps> > :: count == |ss| && allEndAtN(ss, n)
{
}



//ATOM_PLACEHOLDER_Test

