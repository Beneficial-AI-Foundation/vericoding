pub fn power_of_list_elements(l: Seq<int>, n: int) -> (result: Seq<int>)
    requires(n >= 0)
    ensures(|result| == |l|)
    ensures(forall|i: int| 0 <= i < |l| ==> result[i] == power(l[i], n))
{
}

spec fn power(base: int, exponent: int) -> int
    recommends(exponent >= 0)
{
    if exponent == 0 { 1 } else { base * power(base, exponent - 1) }
}