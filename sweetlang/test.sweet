
type Option<T> {
    Some(T) | None
}
fn make_some<T>(val: T) -> Option<T> {
    Option::Some(val)
}

fn get_hkt<C<?>, T>(container: C, get: fn(C, u64) -> T, index: u64, rewrap: fn(T) -> C<T>) -> C<T> {
    
    let value = get(container, index); // automatically inferred to be T
    let wrapped = rewrap(value); // inferred to be C<T>

    wrapped
}

fn use() -> void {
    //let options = list[Some(0), Some(1), Some(2)];
    let first = get_hkt(options, fn(container: List<Option<i32>>, index: u64) -> Option<i32> container_index(container, index), ZERO, fn(v: i32) -> _ Some(v));
    {}
}

type Node {
    | Default
    | Sum(Node, Node)
}
type Nodes {
    nodes: List<Node>
}

fn append_node(nodes: Nodes, node: Node) -> Nodes {
    let ret = new Nodes;
    drop(nodes, node);
    ret
}

fn test() -> void {
    let nodes = new Nodes;
    let nodes = {
        let node = new Node::Default;
        let ret = append_node(nodes, node);
        drop(nodes);
        drop(node);
        ret
    };
    drop(nodes)
}