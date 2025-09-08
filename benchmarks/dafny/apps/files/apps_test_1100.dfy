Given a regular convex polygon with n vertices, draw rays from each vertex to all others.
Rays stop when hitting vertices or intersecting previously drawn rays, creating regions.
A squirrel starts outside and jumps between adjacent regions to collect all walnuts.
Find the minimum number of jumps needed.

predicate ValidInput(n: int)
{
    n >= 3
}

function MinJumps(n: int): int
    requires ValidInput(n)
{
    (n - 2) * (n - 2)
}

method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == MinJumps(n)
{
    result := (n - 2) * (n - 2);
}
