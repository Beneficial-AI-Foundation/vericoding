//IMPL 

// MULTISETS

method multiplicity_examples<T> ()
{
    // Create some multisets
    var m1: multiset<int> := multiset{1, 2, 2, 3};
    var m2: multiset<int> := multiset{2, 3, 3, 4};
    
    // Union of multisets
    var union := m1 + m2;
    assert union == multiset{1, 2, 2, 2, 3, 3, 3, 4};
    
    // Intersection of multisets
    var intersection := m1 * m2;
    /* code modified by LLM (iteration 1): Fixed intersection assertion - multiset intersection takes minimum multiplicity of each element */
    assert intersection == multiset{2, 3};
    
    // Difference of multisets
    var difference := m1 - m2;
    /* code modified by LLM (iteration 1): Fixed difference assertion - multiset difference subtracts multiplicities */
    assert difference == multiset{1, 2};
    
    // Check multiplicity
    assert m1[2] == 2;  // element 2 appears twice in m1
    assert m1[1] == 1;  // element 1 appears once in m1
    assert m1[5] == 0;  // element 5 doesn't appear in m1
    
    // Check membership
    assert 2 in m1;
    assert 5 !in m1;
    
    // Size of multiset
    assert |m1| == 4;
    
    // Empty multiset
    var empty: multiset<int> := multiset{};
    assert |empty| == 0;
    
    // Convert from sequence
    var seq := [1, 2, 2, 3];
    var from_seq := multiset(seq);
    assert from_seq == m1;
}