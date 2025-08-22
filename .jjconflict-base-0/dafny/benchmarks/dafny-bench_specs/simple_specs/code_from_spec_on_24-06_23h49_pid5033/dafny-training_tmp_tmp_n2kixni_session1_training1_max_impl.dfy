//IMPL
method max(x: int, y: int) returns (m: int)
requires true
ensures true
{
    if x >= y {
        m := x;
    } else {
        m := y;
    }
}

/**
 * Example 1.
 * 
 * Try to prove 
 * 1. the final assert statement (uncomment it and you may need to strengthen pre condition).
 * 2. termination, propose a decrease clause (to replace *)
 */