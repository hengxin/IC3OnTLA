import parse
import typecheck
import separator.logic as logic
import separator.separate as separate
import ic3
def main() -> None:
    #ic3.IC3(T,P)
    # 测试一下，假设有一个文件example.tla
    #info = parse.read_tla_file("./spec/two_phase_commit.tla")
    # 打印字典
    #print(info)
    #check.apalache_typecheck("TwoPhaseTyped")
    #F = [[]]
    #F[0] = ["Init","Safety"]
    #ic3.conjuction(F[0])
    #write2spec.updateFrameInv("./spec/tpcommit.tla",1,"abc")
    #result = check.apalache_check_sat("TwoPhaseTyped","P","P","InitializeRM",0)
    #test_for_parse_module()
    #test_for_type_check()
    #test_for_logic_read()
    #test_peterson()
    ic3.FOL_IC3("two_phase_commit")
    return True

def test_for_parse_module():
    parse.parse_tla_information_with_json()
    return True

def test_for_type_check():
    typechecker123 = typecheck.TypeChecker()
    typechecker123.typecheck()
    return True
def test_for_logic_read():
    typechecker123 = typecheck.TypeChecker()
    typechecker123.typecheck()
    state1 = logic.State()
    state1.load(typechecker123)
    state1.update(True,0,"tpcommit")
    state2 = logic.State()
    state2.load(typechecker123)
    state2.update(True, 1, "tpcommit")
    state3 = logic.State()
    state3.load(typechecker123)
    state3.update(False, 0, "tpcommit")
    separator = separate.Separator()
    print(separator.separate.collapse(state1,typechecker123,[]))
    print(separator.separate.collapse(state2,typechecker123,[]))
    print(separator.separate.collapse(state3,typechecker123,[]))
def test_tcommit():
    typechecker123 = typecheck.TypeChecker()
    typechecker123.typecheck()
    state1 = logic.State()
    state1.load(typechecker123)
    state1.update(True, 0, "tcommit")
    state2 = logic.State()
    state2.load(typechecker123)
    state2.update(True, 1, "tcommit")
    state3 = logic.State()
    state3.load(typechecker123)
    state3.update(False, 2, "tcommit")
    separator = separate.Separator()
    separator.add_state(state1)
    separator.add_state(state2)
    separator.add_state(state3)
    separator.load(typechecker123)
    separator.collapsed_pool.load(typechecker123)
    print(separator.separate([0, 1], [2], [], 5, 3))
def test_tpcommit():
    typechecker123 = typecheck.TypeChecker()
    typechecker123.typecheck()
    state1 = logic.State()
    state1.load(typechecker123)
    state1.update(True, 0, "tpcommit")
    state2 = logic.State()
    state2.load(typechecker123)
    state2.update(True, 1, "tpcommit")
    state3 = logic.State()
    state3.load(typechecker123)
    state3.update(False, 4, "tpcommit")
    state4 = logic.State()
    state4.load(typechecker123)
    state4.update(False, 5, "tpcommit")
    separator = separate.Separator()
    separator.add_state(state1)
    separator.add_state(state2)
    separator.add_state(state3)
    separator.add_state(state4)
    separator.load(typechecker123)
    separator.collapsed_pool.load(typechecker123)
    print(separator.separate([0, 1], [2, 3], [], 5, 3))
def test_tpcommit1():
    typechecker123 = typecheck.TypeChecker()
    typechecker123.typecheck()
    state1 = logic.State()
    state1.load(typechecker123)
    state1.update(True, 0, "tpcommit1")
    state2 = logic.State()
    state2.load(typechecker123)
    state2.update(True, 1, "tpcommit1")
    state3 = logic.State()
    state3.load(typechecker123)
    state3.update(False, 2, "tpcommit1")
    separator = separate.Separator()
    separator.add_state(state1)
    separator.add_state(state2)
    separator.add_state(state3)
    separator.load(typechecker123)
    separator.collapsed_pool.load(typechecker123)
    print(separator.separate([0, 1], [2], [], 5, 3))
def test_peterson():
    typechecker123 = typecheck.TypeChecker()
    typechecker123.typecheck()
    state1 = logic.State()
    state1.load(typechecker123)
    state1.update(True, 0, "peterson")
    state2 = logic.State()
    state2.load(typechecker123)
    state2.update(True, 1, "peterson")
    state3 = logic.State()
    state3.load(typechecker123)
    state3.update(False, 2, "peterson")
    state4 = logic.State()
    state4.load(typechecker123)
    state4.update(False, 3, "peterson")
    separator = separate.Separator()
    separator.add_state(state1)
    separator.add_state(state2)
    separator.add_state(state3)
    separator.add_state(state4)
    separator.load(typechecker123)
    separator.collapsed_pool.load(typechecker123)
    print(separator.separate([0, 1], [2, 3], [], 5, 3))
def test_lockserv():
    typechecker123 = typecheck.TypeChecker()
    typechecker123.typecheck()
    state1 = logic.State()
    state1.load(typechecker123)
    state1.update(True, 0, "lockserv")
    state2 = logic.State()
    state2.load(typechecker123)
    state2.update(True, 1, "lockserv")
    state3 = logic.State()
    state3.load(typechecker123)
    state3.update(False, 2, "lockserv")
    state4 = logic.State()
    state4.load(typechecker123)
    state4.update(False, 3, "lockserv")
    separator = separate.Separator()
    separator.add_state(state1)
    separator.add_state(state2)
    separator.add_state(state3)
    separator.add_state(state4)
    separator.load(typechecker123)
    separator.collapsed_pool.load(typechecker123)
    print(separator.separate([0, 1], [2, 3], [], 5, 3))
def test_tpcommit3():
    typechecker123 = typecheck.TypeChecker()
    typechecker123.typecheck()
    state1 = logic.State()
    state1.load(typechecker123)
    state1.update(True, 0, "tpcommit3")
    state2 = logic.State()
    state2.load(typechecker123)
    state2.update(True, 1, "tpcommit3")
    state3 = logic.State()
    state3.load(typechecker123)
    state3.update(False, 2, "tpcommit3")
    separator = separate.Separator()
    separator.add_state(state1)
    separator.add_state(state2)
    separator.add_state(state3)
    separator.load(typechecker123)
    separator.collapsed_pool.load(typechecker123)
    print(separator.separate([0, 1], [2], [], 5, 3))
if __name__ == "__main__":
    main()