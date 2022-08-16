procedure assume_false_assert_false() {
    var x: int;

    havoc x;
    if (x > 0)
    {
        assume false;
        x := x - 1;
    }

    assert false;
}