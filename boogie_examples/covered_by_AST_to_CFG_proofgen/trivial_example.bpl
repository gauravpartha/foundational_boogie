function f(x: int) : bool;

procedure p(x: int) {
    var a : int;

    assume f(a);
    assert f(a);
}
