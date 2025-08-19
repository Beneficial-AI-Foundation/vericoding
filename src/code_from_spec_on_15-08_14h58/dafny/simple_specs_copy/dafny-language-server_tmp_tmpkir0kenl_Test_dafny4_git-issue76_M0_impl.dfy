//IMPL 

// The verification of the following methods requires knowledge
// about the injectivity of sequence displays.

method M0()
{
    // Demonstrate injectivity of sequence displays
    // If [a, b] == [c, d], then a == c and b == d
    var a, b, c, d := 1, 2, 3, 4;
    var seq1 := [a, b];
    var seq2 := [c, d];
    
    // The verifier automatically knows that if seq1 == seq2,
    // then their elements must be equal
    if seq1 == seq2 {
        assert a == c;
        assert b == d;
    }
    
    // Another example with more complex sequences
    var x, y := [1, 2, 3], [4, 5, 6];
    if [x, y] == [[1, 2, 3], [4, 5, 6]] {
        assert x == [1, 2, 3];
        assert y == [4, 5, 6];
    }
}