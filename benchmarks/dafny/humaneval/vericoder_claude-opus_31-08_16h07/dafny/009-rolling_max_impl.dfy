datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires exists i : int :: mx == Some(i)
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
// Helper lemma to prove that the rolling max property is maintained
lemma rolling_max_property(numbers: seq<int>, result: seq<int>, k: int)
    requires 0 <= k < |numbers|
    requires |result| == k + 1
    requires forall i :: 0 <= i < k ==> numbers[i] <= result[i]
    requires forall i :: 0 <= i < k ==> result[i] <= result[i + 1]
    requires k > 0 ==> result[k] == if numbers[k] > result[k-1] then numbers[k] else result[k-1]
    requires k == 0 ==> result[k] == numbers[k]
    ensures numbers[k] <= result[k]
    ensures k > 0 ==> result[k-1] <= result[k]
{
    // The proof follows from the definition of how we compute result[k]
}
// </vc-helpers>

// <vc-spec>
method rolling_max(numbers: seq<int>) returns (result : seq<int>)
    // post-conditions-start
    ensures |numbers| == |result|
    ensures forall i : int :: i >= 0 && i < |numbers| ==> numbers[i] <= result[i]
    ensures forall i : int :: i >= 0 && i + 1 < |numbers| ==> result[i] <= result[i + 1]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if |numbers| == 0 {
        return [];
    }
    
    result := [numbers[0]];
    var i := 1;
    
    while i < |numbers|
        invariant 1 <= i <= |numbers|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> numbers[j] <= result[j]
        invariant forall j :: 0 <= j < i - 1 ==> result[j] <= result[j + 1]
    {
        var max_so_far := if numbers[i] > result[i-1] then numbers[i] else result[i-1];
        result := result + [max_so_far];
        i := i + 1;
    }
}
// </vc-code>

