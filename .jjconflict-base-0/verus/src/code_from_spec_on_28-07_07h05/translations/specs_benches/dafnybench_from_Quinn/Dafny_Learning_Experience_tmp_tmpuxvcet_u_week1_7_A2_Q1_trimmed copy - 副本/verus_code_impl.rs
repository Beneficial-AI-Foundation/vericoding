requires count_index < |a|
    requires b.Length >= |a|
    ensures p <= count_index + 1
    modifies b
/* code modified by LLM (iteration 3): removed stray decreases clause and fixed implementation */
{
    var result := 0;
    var i := 0;
    while i <= count_index
        invariant i <= count_index + 1
        invariant result <= i
    {
        if i < |a| && a[i] % 2 == 0 {
            result := result + 1;
        }
        i := i + 1;
    }
    if count_index < b.Length {
        b[count_index] := result;
    }
    p := result;
}

//IMPL foo_precompute
method foo_precompute(a: seq<int>, b: array<int>)
    requires b.Length >= |a|
    modifies b
/* code modified by LLM (iteration 3): fixed implementation with proper loop structure */
{
    var i := 0;
    while i < |a|
        invariant i <= |a|
    {
        var count_val := 0;
        var j := 0;
        while j <= i
            invariant j <= i + 1
            invariant count_val <= j
        {
            if j < |a| && a[j] % 2 == 0 {
                count_val := count_val + 1;
            }
            j := j + 1;
        }
        b[i] := count_val;
        i := i + 1;
    }
}

//IMPL compute_count
method compute_count(count_index: nat, a: seq<int>, b: array<int>) returns (p: nat)
    requires count_index < |a|
    requires b.Length >= |a|
    ensures p <= count_index + 1
    modifies b
/* code modified by LLM (iteration 3): fixed implementation */
{
    var result := 0;
    var i := 0;
    while i <= count_index
        invariant i <= count_index + 1
        invariant result <= i
    {
        if i < |a| && a[i] % 2 == 0 {
            result := result + 1;
        }
        i := i + 1;
    }
    p := result;
}

//IMPL precompute
method precompute(a: seq<int>, b: array<int>) returns (p: nat)
    requires b.Length >= |a|
    ensures p <= |a|
    modifies b
/* code modified by LLM (iteration 3): fixed implementation */
{
    foo_precompute(a, b);
    p := |a|;
}

//IMPL evens
method evens(a: seq<int>) returns (result: seq<seq<int>>)
/* code modified by LLM (iteration 3): fixed implementation */
{
    var temp: seq<seq<int>> := [];
    var i := 0;
    while i < |a|
        invariant i <= |a|
        invariant |temp| <= i
    {
        if a[i] % 2 == 0 {
            var inner: seq<int> := [a[i]];
            temp := temp + [inner];
        }
        i := i + 1;
    }
    result := temp;
}

//IMPL mult
method mult(x: int, y: int) returns (r: int)
    ensures r == x * y
/* code modified by LLM (iteration 3): fixed implementation */
{
    r := x * y;
}