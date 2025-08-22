//ATOM
datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)


//ATOM

datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)


//ATOM

function serialise<V>(t : Tree<V>) : seq<Code<V>> 
{
 match t {
  case Leaf(v) => [ CLf(v) ]
  case SingleNode(v, t) => serialise(t) + [ CSNd(v) ]
  case DoubleNode(v, t1, t2) => serialise(t2) + serialise(t1) + [ CDNd(v) ]
 }
}


//IMPL testSerializeWithAllElements

method testSerializeWithAllElements()
{
    // Test Leaf
    var leaf := Leaf(1);
    var leafSerialized := serialise(leaf);
    
    // Test SingleNode
    var singleNode := SingleNode(2, Leaf(3));
    var singleNodeSerialized := serialise(singleNode);
    
    // Test DoubleNode
    var doubleNode := DoubleNode(4, Leaf(5), Leaf(6));
    var doubleNodeSerialized := serialise(doubleNode);
    
    // More complex tree with all elements
    var complexTree := DoubleNode(7, 
                                 SingleNode(8, Leaf(9)), 
                                 DoubleNode(10, Leaf(11), Leaf(12)));
    var complexSerialized := serialise(complexTree);
}