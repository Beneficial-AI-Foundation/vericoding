function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method sum_product(numbers: seq<int>) returns (s : int, p : int)
    // post-condition-start
    ensures s == sum(numbers)
    ensures p == prod(numbers)
    // post-condition-end
// </vc-spec>
// <vc-code>
s := sum(numbers);
p := prod(numbers);
// </vc-code>

