procedure assert_false_in_if_2() {
    var x: int;

    havoc x;
    if (x != 8)
    {
        assert false;
    }

    x := 7;
    assert x == 7;
}