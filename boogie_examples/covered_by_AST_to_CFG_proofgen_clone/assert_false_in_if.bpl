procedure assert_false_in_if() {
    var x: int;

    havoc x;
    if (x != 8)
    {
        assert false;
    }
}