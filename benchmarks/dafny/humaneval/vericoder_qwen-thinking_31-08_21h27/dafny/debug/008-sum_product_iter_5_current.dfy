function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}

// <vc-helpers>
function sum_prod_pair(numbers: seq<int>) returns (sub_sum: int, sub_prod: int)
    ensures sub_sum == sum(numbers)
    ensures sub_prod == prod(numbers)
{
    if |numbers| == 0 {
        sub_sum := 0;
        sub_prod := 1;
    } else {
        var (s, p) := sum_prod_pair(numbers[1..]);
        sub_sum := numbers[0] + s;
        sub_prod := numbers[0] * p;
    }
}
// </vc-helpers>

// <vc-spec>
method sum_product(numbers: seq<int>) returns (s : int, p : int)
    // post-condition-start
    ensures s == sum(numbers)
    ensures p == prod(numbers)
    // post-condition-end
// </vc-spec>
// <vc-code>
{
    if |numbers| == 0 {
        s := 0;
        p := 1;
    } else {
        var (sub_sum, sub_prod) := sum_prod_pair(numbers[1..]);
        s := numbers[0] + sub_sum;
        p := numbers[0] * sub_prod;
    }
}
// </vc-code>

