method multiplicity_examples<T> ()
{
    // Create some multisets
    var m1: multiset<int> := multiset{1, 2, 2, 3, 3, 3};
    var m2: multiset<int> := multiset{2, 3, 4, 4};
    
    // Demonstrate multiplicity (count of elements)
    assert m1[1] == 1;  // element 1 appears once
    assert m1[2] == 2;  // element 2 appears twice
    assert m1[3] == 3;  // element 3 appears three times
    assert m1[4] == 0;  // element 4 doesn't appear
    
    // Multiset union
    var union := m1 + m2;
    /* code modified by LLM (iteration 1): Fixed assertion - m2[2] == 1, so union[2] == 2 + 1 == 3 */
    assert union[2] == 3;  // 2 from m1 + 1 from m2
    assert union[3] == 4;  // 3 from m1 + 1 from m2
    
    // Multiset difference
    var diff := m1 - m2;
    /* code modified by LLM (iteration 2): Fixed assertion - m1[2] == 2 and m2[2] == 1, so max(2-1, 0) == 1 */
    assert diff[2] == 1;   // max(2-1, 0) = 1
    assert diff[3] == 2;   // max(3-1, 0) = 2
    assert diff[1] == 1;   // 1 is only in m1
    
    // Multiset intersection
    var inter := m1 * m2;
    /* code modified by LLM (iteration 3): Fixed assertion - m2[2] == 1, so min(2, 1) == 1 */
    assert inter[2] == 1;  // min(2, 1) = 1
    assert inter[3] == 1;  // min(3, 1) = 1
    assert inter[1] == 0;  // min(1, 0) = 0
    
    // Convert from sequence
    /* code modified by LLM (iteration 1): Changed variable name from 'seq' to 'sequence' since 'seq' is a reserved keyword in Dafny */
    var sequence := [1, 1, 2, 3, 2];
    /* code modified by LLM (iteration 1): Fixed multiset conversion syntax */
    var fromSeq := multiset(sequence);
    assert fromSeq[1] == 2;
    assert fromSeq[2] == 2;
    assert fromSeq[3] == 1;
    
    // Empty multiset
    var empty: multiset<int> := multiset{};
    assert |empty| == 0;
    assert empty[5] == 0;
    
    // Size/cardinality
    assert |m1| == 6;  // 1 + 2 + 3 = 6 total elements
    assert |m2| == 4;  // 1 + 1 + 2 = 4 total elements
}