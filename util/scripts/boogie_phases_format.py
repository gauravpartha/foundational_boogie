import sys

def transform(inputt, outputt_base):
    with open(inputt, "r") as f:
        for count, block in enumerate(f.read().split("after")):
            outputt_name = outputt_base + "_{0}_{1}.txt".format(count, mapping[count])
            print(count)
            with open(outputt_name, "w") as f1:
                f1.write(block)

mapping = ["original_impl", "desugared_cmds", "dag", "unified_exit", "insert_pre_post", "add_empty_blocks_join", "passification", "peep-hole"]

boogieLogFile = sys.argv[1]

logFileName = boogieLogFile.split(".log")[0]

print(logFileName)

transform(boogieLogFile, logFileName)

