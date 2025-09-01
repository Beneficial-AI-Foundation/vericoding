

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method max_element(l : seq<int>) returns (result : int)
    // pre-conditions-start
    requires |l| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |l| ==> l[i] <= result
    ensures exists i : int :: i >= 0 && i < |l| && l[i] == result
    // post-conditions-end
// </vc-spec>
// <vc-code>
var result := l[0];
for i := 1 to |l| - 1 {
    invariant forall j : int :: 0 <= j < i ==> l[j] <= result;
    if l[i] > result {
        result := l[i];
    }
}
return result;
// </vc-code>

