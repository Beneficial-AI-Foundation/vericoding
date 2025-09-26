// <vc-preamble>
predicate ValidInput(a: int)
{
    0 <= a <= 35
}

function ExpectedSequence(): seq<int>
{
    [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8092, 16184, 32368, 64736, 129472, 258944, 517888, 1035776, 2071552, 4143104, 8286208, 16572416, 33144832, 66289664, 132579328, 265158656, 530317312, 1060634624, 2121269248, 4242538496, 8485076992, 16970153984, 33940307968]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Solve(a: int) returns (result: int)
    requires ValidInput(a)
    ensures result == ExpectedSequence()[a]
// </vc-spec>
// <vc-code>
{
    var sequence := ExpectedSequence();
    result := sequence[a];
}
// </vc-code>
