procedure q() {
    var x : int;

    x := 0;
    goto label1;

    x := 2;

label1:
    assert x == 0;
}
