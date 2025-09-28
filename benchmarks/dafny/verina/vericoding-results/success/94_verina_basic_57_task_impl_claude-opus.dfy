// <vc-preamble>
/* Helper function to recursively count elements less than threshold */
function CountLessThanSpec(numbers: seq<int>, threshold: int): nat
    decreases |numbers|
{
    if |numbers| == 0 then
        0
    else
        var first := numbers[0];
        var rest := numbers[1..];
        if first < threshold then
            1 + CountLessThanSpec(rest, threshold)
        else
            CountLessThanSpec(rest, threshold)
}
// </vc-preamble>

// <vc-helpers>
lemma CountLessThanSpecAppend(s1: seq<int>, s2: seq<int>, threshold: int)
    ensures CountLessThanSpec(s1 + s2, threshold) == CountLessThanSpec(s1, threshold) + CountLessThanSpec(s2, threshold)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        var first := s1[0];
        var rest := s1[1..];
        assert s1 + s2 == [first] + (rest + s2);
        CountLessThanSpecAppend(rest, s2, threshold);
    }
}
// </vc-helpers>

// <vc-spec>
method CountLessThan(numbers: array<int>, threshold: int) returns (result: nat)
    ensures result == CountLessThanSpec(numbers[..], threshold)
// </vc-spec>
// <vc-code>
{
    result := 0;
    var i := 0;
    
    while i < numbers.Length
        invariant 0 <= i <= numbers.Length
        invariant result == CountLessThanSpec(numbers[..i], threshold)
    {
        if numbers[i] < threshold {
            result := result + 1;
        }
        
        assert numbers[..i+1] == numbers[..i] + [numbers[i]];
        CountLessThanSpecAppend(numbers[..i], [numbers[i]], threshold);
        
        i := i + 1;
    }
    
    assert numbers[..] == numbers[..numbers.Length];
}
// </vc-code>
