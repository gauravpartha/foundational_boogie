procedure assert_false_in_if_3() {
    var x: int;

    havoc x;
    if (*)
    {
        assert false;
    }

    x := 7;
    assert x == 7;
}