// ATOM 
spec fn reverse(xs: Seq<nat>) -> Seq<nat>
{
    if xs == seq![] then seq![] else reverse(xs.subrange(1, xs.len() as int)) + seq![xs[0]]
}

// ATOM 
proof fn ReverseAppendDistr(xs: Seq<nat>, ys: Seq<nat>)
    ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{
}

// ATOM 
proof fn ReverseInvolution(xxs: Seq<nat>)
    ensures reverse(reverse(xxs)) == xxs
{
}