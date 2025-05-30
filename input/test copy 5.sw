
type Option<T> {
    Some(T) | None
}
fn make_some<T>(val: T) -> Option<T> {
    Option::Some(val)
}

fn get_hkt<C<?>, T>(container: C, get: fn(C, u64) -> T, index: u64, rewrap: fn(T) -> C<T>) -> C<T> {
    
    //let value = get(container, index) // automatically inferred to be T
    //let wrapped = rewrap(value) // inferred to be C<T>

    wrapped
}

fn use() -> void {
    //let options = list[Some(0), Some(1), Some(2)];
    //let first = get_hkt(options, |container, index| container[index], 0, |v| Some(v));

}

type Node {
    | Default
    | Sum(Node, Node)
}
type Nodes {
    nodes: List<Node>
}

fn append_node(nodes: Nodes, node: Node) -> Nodes {
    let ret = new Nodes {
        nodes: append_list(nodes.nodes, node)
    };
    drop(nodes, node);
    ret
}

fn test() -> void {
    let nodes = new Nodes {
        nodes: new_list()
    };
    let nodes = {
        let node = new Node::Default;
        let _ = append_node(nodes, node)
        drop(nodes);
        drop(node);
        _
    }
    drop(nodes);
}