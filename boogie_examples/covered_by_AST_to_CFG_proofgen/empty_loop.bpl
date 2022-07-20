procedure p() {
    var x: int;

    x := 0;
    while (x > 0)
        invariant x >= 0; {}
    assert x == 0;
}