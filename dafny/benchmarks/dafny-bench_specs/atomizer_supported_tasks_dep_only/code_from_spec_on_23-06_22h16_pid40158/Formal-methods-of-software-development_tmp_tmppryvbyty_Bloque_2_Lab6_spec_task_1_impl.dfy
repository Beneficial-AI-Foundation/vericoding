/* code modified by LLM (iteration 4): Added decreases clause for termination */
function sum(v: seq<int>): int
    decreases |v|
{
    if |v| == 0 then 0
    else v[0] + sum(v[1..])
}

/* code modified by LLM (iteration 4): Fixed helper lemma with correct logic */
lemma SumExtend(v: seq<int>, i: int)
    requires 0 <= i < |v|
    ensures sum(v[0..i+1]) == sum(v[0..i]) + v[i]
{
    if i == 0 {
        /* code modified by LLM (iteration 4): Base case - direct computation */
        assert v[0..0] == [];
        assert v[0..1] == [v[0]];
        assert sum(v[0..0]) == 0;
        assert sum(v[0..1]) == v[0] + sum([]) == v[0];
    } else {
        /* code modified by LLM (iteration 4): Inductive case using definition of sum */
        assert v[0..i+1] == [v[0]] + v[1..i+1];
        assert sum(v[0..i+1]) == v[0] + sum(v[1..i+1]);
        
        assert v[0..i] == [v[0]] + v[1..i];
        assert sum(v[0..i]) == v[0] + sum(v[1..i]);
        
        /* code modified by LLM (iteration 4): Apply lemma to suffix */
        SumExtend(v[1..], i-1);
        assert sum(v[1..][0..i]) == sum(v[1..][0..i-1]) + v[1..][i-1];
        assert v[1..][0..i] == v[1..i];
        assert v[1..][0..i-1] == v[1..i-1];
        assert v[1..][i-1] == v[i];
        
        /* code modified by LLM (iteration 4): Complete the proof */
        assert sum(v[1..i]) == sum(v[1..i-1]) + v[i];
        assert sum(v[1..i+1]) == v[1] + sum(v[2..i+1]);
        assert sum(v[1..i+1]) == sum(v[1..i]) + v[i];
    }
}

method vector_Sum(v:seq<int>) returns (x:int)
ensures x == sum(v) 
{
    /* code modified by LLM (iteration 4): Corrected implementation with proper lemma usage */
    x := 0;
    var i := 0;
    while i < |v|
        invariant 0 <= i <= |v|
        invariant x == sum(v[0..i])
    {
        /* code modified by LLM (iteration 4): Call lemma before updating x */
        SumExtend(v, i);
        x := x + v[i];
        i := i + 1;
    }
}