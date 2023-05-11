#use Apalache to check
import subprocess
import re
def apalache_typecheck(spec):
    # 指定TLA+规范文件和Apalache可执行文件路径
    spec_file = "spec/" + spec + ".tla"
    apalache_exec = "./tool/apalache.jar"

    # 构造Apalache的命令行参数
    cmd = ["java", "-jar", apalache_exec, "typecheck", "--features=no-rows", "--output=spec2json/"+spec+"_output.json", spec_file]

    # 使用subprocess模块执行Apalache命令
    result = subprocess.run(cmd, capture_output=True, text=True)

    # 打印Apalache的输出结果
    print(result.stdout)
    match = re.search(r"EXITCODE: (.*)", result.stdout)
    if match.group(1) == "OK":
        return "OK"
    elif match.group(1) == "ERROR":
        return "ERROR"
    else:
        return "Unknown Error"

def apalache_check_sat(spec,init,inv,cinit,length,state_index):
    # 指定TLA+规范文件和Apalache可执行文件路径
    spec_file = "spec/" + spec + ".tla"
    apalache_exec = "./tool/apalache.jar"

    # 构造Apalache的命令行参数
    if cinit is not None:
        cmd = ["java", "-jar", apalache_exec, "check", "--output-traces","--init=" + init, "--cinit=" + cinit,
               "--inv=" + inv,
               "--length=" + str(length), spec_file]
    else:
        cmd = ["java", "-jar", apalache_exec, "check", "--output-traces","--init=" + init, "--inv=" + inv,
               "--length=" + str(length), spec_file]

    # 使用subprocess模块执行Apalache命令
    result = subprocess.run(cmd, capture_output=True, text=True)

    # 打印Apalache的输出结果
    match = re.search(r"EXITCODE: (.*)", result.stdout)
    label = True
    if match.group(1) == "OK":
        label = True
    else:
        label = False
    match = re.search(r"Output directory: (.*)", result.stdout)
    if label:
        dir = match.group(1) + "/example.tla"
    else:
        dir = match.group(1) + "/violation.tla"
    with open(dir, "r") as f:
        lines = f.readlines()
        State0 = ""
        State1 = ""
        for i in range(0, len(lines)):
            if lines[i] == "State0 ==\n":
                if label:
                    State0 += "Positive_State" + str(state_index) + " ==\n"
                else:
                    State0 += "Negative_State" + str(state_index) + " ==\n"
                state_index += 1
                for j in range(i + 1, len(lines)):
                    if lines[j] != "\n":
                        State0 += lines[j]
                    else:
                        break
            elif lines[i] == "State1 ==\n":
                if label:
                    State1 += "Positive_State" + str(state_index) + " ==\n"
                else:
                    State1 += "Negative_State" + str(state_index) + " ==\n"
                state_index += 1
                for j in range(i + 1, len(lines)):
                    if lines[j] != "\n":
                        State1 += lines[j]
                    else:
                        break
    if State0 != "":
        State0 += "End\n\n"
    if State1 != "":
        State1 += "End\n\n"
    writedir = "/Users/fruitfighter/Desktop/IC3onTLA+/state/two_phase_commit_states.tla"
    with open(writedir, "a") as f:
        # 写入内容到文件末尾
        f.write(State0)
        f.write(State1)
    return label,state_index


def apalache_check_inv(spec,init,inv,cinit,length,state_index):
    # 指定TLA+规范文件和Apalache可执行文件路径
    spec_file = "spec/" + spec + ".tla"
    apalache_exec = "./tool/apalache.jar"

    # 构造Apalache的命令行参数
    if cinit is not None:
        cmd = ["java", "-jar", apalache_exec, "check", "--output-traces","--init=" + init, "--cinit=" + cinit,
               "--inv=" + inv,
               "--length=" + str(length), spec_file]
    else:
        cmd = ["java", "-jar", apalache_exec, "check", "--output-traces","--init=" + init, "--inv=" + inv,
               "--length=" + str(length), spec_file]

    # 使用subprocess模块执行Apalache命令
    result = subprocess.run(cmd, capture_output=True, text=True)
    # 打印Apalache的输出结果
    match = re.search(r"EXITCODE: (.*)", result.stdout)
    label = True
    if match.group(1) == "OK":
        label = True
    else:
        return False,0
    match = re.search(r"Output directory: (.*)", result.stdout)
    dir = match.group(1) + "/example.tla"
    with open(dir, "r") as f:
        lines = f.readlines()
        State0 = ""
        State1 = ""
        for i in range(0, len(lines)):
            if lines[i] == "State0 ==\n":
                State0 += "Positive_State" + str(state_index) + " ==\n"
                state_index += 1
                for j in range(i + 1, len(lines)):
                    if lines[j] != "\n":
                        State0 += lines[j]
                    else:
                        break
            elif lines[i] == "State1 ==\n":
                State1 += "Positive_State" + str(state_index) + " ==\n"
                state_index += 1
                for j in range(i + 1, len(lines)):
                    if lines[j] != "\n":
                        State1 += lines[j]
                    else:
                        break
    if State0 != "":
        State0 += "End\n\n"
    if State1 != "":
        State1 += "End\n\n"
    writedir = "/Users/fruitfighter/Desktop/IC3onTLA+/state/two_phase_commit_states.tla"
    with open(writedir, "a") as f:
        # 写入内容到文件末尾
        f.write(State0)
        f.write(State1)
    return label, state_index

def apalache_check_safe(spec,init,inv,cinit,length,state_index):
    # 指定TLA+规范文件和Apalache可执行文件路径
    spec_file = "spec/" + spec + ".tla"
    apalache_exec = "./tool/apalache.jar"

    # 构造Apalache的命令行参数
    if cinit is not None:
        cmd = ["java", "-jar", apalache_exec, "check", "--output-traces","--init=" + init, "--cinit=" + cinit,
               "--inv=" + inv,
               "--length=" + str(length), spec_file]
    else:
        cmd = ["java", "-jar", apalache_exec, "check", "--output-traces","--init=" + init, "--inv=" + inv,
               "--length=" + str(length), spec_file]

    # 使用subprocess模块执行Apalache命令
    result = subprocess.run(cmd, capture_output=True, text=True)
    # 打印Apalache的输出结果
    match = re.search(r"EXITCODE: (.*)", result.stdout)
    label = True
    if match.group(1) == "OK":
        return True,0,None
    else:
        label = False
    match = re.search(r"Output directory: (.*)", result.stdout)
    end_str = ""
    dir = match.group(1) + "/violation.tla"
    with open(dir, "r") as f:
        lines = f.readlines()
        State0 = ""
        State1 = ""
        for i in range(0, len(lines)):
            if lines[i] == "State0 ==\n":
                State0 += "Negative_State" + str(state_index) + " ==\n"
                for j in range(i + 1, len(lines)):
                    if lines[j] != "\n":
                        end_str += lines[j]
                        State0 += lines[j]
                    else:
                        break
            elif lines[i] == "State1 ==\n":
                end_str = ""
                State1 += "Negative_State" + str(state_index) + " ==\n"
                for j in range(i + 1, len(lines)):
                    if lines[j] != "\n":
                        end_str += lines[j]
                        State1 += lines[j]
                    else:
                        break
    end_state = ""
    if State0 != "":
        end_state = State0
    if State1 != "":
        end_state = State1
    writedir = "/Users/fruitfighter/Desktop/IC3onTLA+/state/two_phase_commit_states.tla"
    with open(writedir, "a") as f:
        # 写入内容到文件末尾
        f.write(end_state+"End\n\n")
    state_index += 1
    return label, state_index, end_str

def apalache_check_init(spec,init,inv,cinit,length):
    # 指定TLA+规范文件和Apalache可执行文件路径
    spec_file = "spec/" + spec + ".tla"
    apalache_exec = "./tool/apalache.jar"

    # 构造Apalache的命令行参数
    if cinit is not None:
        cmd = ["java", "-jar", apalache_exec, "check","--init=" + init, "--cinit=" + cinit,
               "--inv=" + inv,
               "--length=" + str(length), spec_file]
    else:
        cmd = ["java", "-jar", apalache_exec, "check","--init=" + init, "--inv=" + inv,
               "--length=" + str(length), spec_file]

    # 使用subprocess模块执行Apalache命令
    result = subprocess.run(cmd, capture_output=True, text=True)
    # 打印Apalache的输出结果
    match = re.search(r"EXITCODE: (.*)", result.stdout)
    if match.group(1) == "OK":
        return True
    else:
        return False
def apalache_check_inductive_relative(spec,init,inv,cinit,length,state_index):
    # 指定TLA+规范文件和Apalache可执行文件路径
    spec_file = "spec/" + spec + ".tla"
    apalache_exec = "./tool/apalache.jar"

    # 构造Apalache的命令行参数
    if cinit is not None:
        cmd = ["java", "-jar", apalache_exec, "check","--init=" + init, "--cinit=" + cinit,
               "--inv=" + inv,
               "--length=" + str(length), spec_file]
    else:
        cmd = ["java", "-jar", apalache_exec, "check","--init=" + init, "--inv=" + inv,
               "--length=" + str(length), spec_file]

    # 使用subprocess模块执行Apalache命令
    result = subprocess.run(cmd, capture_output=True, text=True)
    # 打印Apalache的输出结果
    match = re.search(r"EXITCODE: (.*)", result.stdout)
    label = True
    if match.group(1) == "OK":
        return True, 0,None
    else:
        label = False
    match = re.search(r"Output directory: (.*)", result.stdout)
    dir = match.group(1) + "/violation.tla"
    end_str = ""
    with open(dir, "r") as f:
        lines = f.readlines()
        State0 = ""
        State1 = ""
        for i in range(0, len(lines)):
            if lines[i] == "State0 ==\n":
                State0 += "Negative_State" + str(state_index) + " ==\n"
                for j in range(i + 1, len(lines)):
                    if lines[j] != "\n":
                        end_str += lines[j]
                        State0 += lines[j]
                    else:
                        break
            elif lines[i] == "State1 ==\n":
                end_str = ""
                State1 += "Negative_State" + str(state_index) + " ==\n"
                for j in range(i + 1, len(lines)):
                    if lines[j] != "\n":
                        end_str += lines[j]
                        State1 += lines[j]
                    else:
                        break
    end_state = ""
    if State0 != "":
        end_state = State0
    if State1 != "":
        end_state = State1
    writedir = "/Users/fruitfighter/Desktop/IC3onTLA+/state/two_phase_commit_states.tla"
    with open(writedir, "a") as f:
        # 写入内容到文件末尾
        f.write(end_state+"End\n\n")
    state_index += 1
    return label, state_index, end_str

def apalache_check_inductive(spec,init,inv,cinit,length):
    # 指定TLA+规范文件和Apalache可执行文件路径
    spec_file = "spec/" + spec + ".tla"
    apalache_exec = "./tool/apalache.jar"

    # 构造Apalache的命令行参数
    if cinit is not None:
        cmd = ["java", "-jar", apalache_exec, "check", "--output-traces","--init=" + init, "--cinit=" + cinit,
               "--inv=" + inv,
               "--length=" + str(length), spec_file]
    else:
        cmd = ["java", "-jar", apalache_exec, "check", "--output-traces","--init=" + init, "--inv=" + inv,
               "--length=" + str(length), spec_file]

    # 使用subprocess模块执行Apalache命令
    result = subprocess.run(cmd, capture_output=True, text=True)

    # 打印Apalache的输出结果
    match = re.search(r"EXITCODE: (.*)", result.stdout)
    if match.group(1) == "OK":
        return True
    else:
        return False

def apalache_check_sat_state(spec,init,inv,cinit,length,state_index):
    # 指定TLA+规范文件和Apalache可执行文件路径
    spec_file = "spec/" + spec + ".tla"
    apalache_exec = "./tool/apalache.jar"

    # 构造Apalache的命令行参数
    if cinit is not None:
        cmd = ["java", "-jar", apalache_exec, "check", "--output-traces","--init=" + init, "--cinit=" + cinit,
               "--inv=" + inv,
               "--length=" + str(length), spec_file]
    else:
        cmd = ["java", "-jar", apalache_exec, "check", "--output-traces","--init=" + init, "--inv=" + inv,
               "--length=" + str(length), spec_file]

    # 使用subprocess模块执行Apalache命令
    result = subprocess.run(cmd, capture_output=True, text=True)
    print(result)
    # 打印Apalache的输出结果
    match = re.search(r"EXITCODE: (.*)", result.stdout)
    label = True
    end_str = ""
    if match.group(1) == "OK":
        label = True
    else:
        return False,state_index,None
    match = re.search(r"Output directory: (.*)", result.stdout)
    if label:
        dir = match.group(1) + "/example.tla"
    else:
        dir = match.group(1) + "/violation.tla"
    with open(dir, "r") as f:
        lines = f.readlines()
        State0 = ""
        State1 = ""
        for i in range(0, len(lines)):
            if lines[i] == "State0 ==\n":
                if label:
                    State0 += "Negative_State" + str(state_index) + " ==\n"
                else:
                    State0 += "Positive_State" + str(state_index) + " ==\n"
                state_index += 1
                for j in range(i + 1, len(lines)):
                    if lines[j] != "\n":
                        end_str += lines[j]
                        State0 += lines[j]
                    else:
                        break
            elif lines[i] == "State1 ==\n":
                end_str = ""
                if label:
                    State1 += "Negative_State" + str(state_index) + " ==\n"
                else:
                    State1 += "Positive_State" + str(state_index) + " ==\n"
                state_index += 1
                for j in range(i + 1, len(lines)):
                    if lines[j] != "\n":
                        end_str += lines[j]
                        State1 += lines[j]
                    else:
                        break
    if State0 != "":
        State0 += "End\n\n"
    if State1 != "":
        State1 += "End\n\n"
    writedir = "/Users/fruitfighter/Desktop/IC3onTLA+/state/two_phase_commit_states.tla"
    with open(writedir, "a") as f:
        # 写入内容到文件末尾
        f.write(State0)
        f.write(State1)
    return label,state_index,end_str