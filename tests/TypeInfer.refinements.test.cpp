// This file is part of the Luau programming language and is licensed under MIT License; see LICENSE.txt for details
#include "Luau/Normalize.h"
#include "Luau/Scope.h"
#include "Luau/Type.h"
#include "Luau/TypeInfer.h"

#include "Fixture.h"

#include "doctest.h"

LUAU_FASTFLAG(DebugLuauForceOldSolver)
LUAU_FASTFLAG(DebugLuauAssertOnForcedConstraint)
LUAU_FASTFLAG(LuauRemovePrimitiveTypeConstraintAndSubtypingUnifier)
LUAU_FASTFLAG(LuauIndexingIntoErrorGivesError);

using namespace Luau;

namespace
{

struct MagicInstanceIsA final : MagicFunction
{
    std::optional<WithPredicate<TypePackId>> handleOldSolver(
        TypeChecker& typeChecker,
        const ScopePtr& scope,
        const AstExprCall& expr,
        WithPredicate<TypePackId> withPredicate
    ) override
    {
        if (expr.args.size != 1)
            return std::nullopt;

        auto index = expr.func->as<Luau::AstExprIndexName>();
        auto str = expr.args.data[0]->as<Luau::AstExprConstantString>();
        if (!index || !str)
            return std::nullopt;

        std::optional<LValue> lvalue = tryGetLValue(*index->expr);
        std::optional<TypeFun> tfun = scope->lookupType(std::string(str->value.data, str->value.size));
        if (!lvalue || !tfun)
            return std::nullopt;

        ModulePtr module = typeChecker.currentModule;
        TypePackId booleanPack = module->internalTypes.addTypePack({typeChecker.booleanType});
        return WithPredicate<TypePackId>{booleanPack, {IsAPredicate{std::move(*lvalue), expr.location, tfun->type}}};
    }

    bool infer(const MagicFunctionCallContext&) override
    {
        return false;
    }

    void refine(const MagicRefinementContext& ctx) override
    {
        if (ctx.callSite->args.size != 1 || ctx.discriminantTypes.empty())
            return;

        auto index = ctx.callSite->func->as<Luau::AstExprIndexName>();
        auto str = ctx.callSite->args.data[0]->as<Luau::AstExprConstantString>();
        if (!index || !str)
            return;

        std::optional<TypeId> discriminantTy = ctx.discriminantTypes[0];
        if (!discriminantTy)
            return;

        std::optional<TypeFun> tfun = ctx.scope->lookupType(std::string(str->value.data, str->value.size));
        if (!tfun)
            return;

        LUAU_ASSERT(get<BlockedType>(*discriminantTy));
        asMutable(*discriminantTy)->ty.emplace<BoundType>(tfun->type);
    }
};



struct RefinementExternTypeFixture : BuiltinsFixture
{
    RefinementExternTypeFixture() = default;

    Frontend& getFrontend() override
    {
        if (frontend)
            return *frontend;

        Frontend& f = BuiltinsFixture::getFrontend();
        TypeArena& arena = getFrontend().globals.globalTypes;
        NotNull<Scope> scope{getFrontend().globals.globalScope.get()};

        std::optional<TypeId> rootSuper = std::make_optional(f.builtinTypes->externType);

        unfreeze(arena);
        TypeId vec3 = arena.addType(ExternType{"Vector3", {}, rootSuper, std::nullopt, {}, nullptr, "Test", {}});
        getMutable<ExternType>(vec3)->props = {
            {"X", Property{f.builtinTypes->numberType}},
            {"Y", Property{f.builtinTypes->numberType}},
            {"Z", Property{f.builtinTypes->numberType}},
        };

        TypeId inst = arena.addType(ExternType{"Instance", {}, rootSuper, std::nullopt, {}, nullptr, "Test", {}});

        TypePackId isAParams = arena.addTypePack({inst, f.builtinTypes->stringType});
        TypePackId isARets = arena.addTypePack({f.builtinTypes->booleanType});
        TypeId isA = arena.addType(FunctionType{isAParams, isARets});
        getMutable<FunctionType>(isA)->magic = std::make_shared<MagicInstanceIsA>();

        getMutable<ExternType>(inst)->props = {
            {"Name", Property{f.builtinTypes->stringType}},
            {"IsA", Property{isA}},
        };

        TypeId scriptConnection = arena.addType(ExternType("ExternScriptConnection", {}, inst, std::nullopt, {}, nullptr, "Test", {}));
        TypePackId disconnectArgs = arena.addTypePack({scriptConnection});
        TypeId disconnect = arena.addType(FunctionType{disconnectArgs, f.builtinTypes->emptyTypePack});
        getMutable<ExternType>(scriptConnection)->props = {
            {"Disconnect", Property{disconnect}},
        };

        TypeId folder = f.globals.globalTypes.addType(ExternType{"Folder", {}, inst, std::nullopt, {}, nullptr, "Test", {}});
        TypeId part = f.globals.globalTypes.addType(ExternType{"Part", {}, inst, std::nullopt, {}, nullptr, "Test", {}});
        getMutable<ExternType>(part)->props = {
            {"Position", Property{vec3}},
        };

        TypeId optionalPart = arena.addType(UnionType{{part, f.builtinTypes->nilType}});
        TypeId weldConstraint =
            getFrontend().globals.globalTypes.addType(ExternType{"WeldConstraint", {}, inst, std::nullopt, {}, nullptr, "Test", {}});
        getMutable<ExternType>(weldConstraint)->props = {
            {"Part0", Property{optionalPart}},
            {"Part1", Property{optionalPart}},
        };

        TypeId discriminant = arena.addType(ExternType{"Discriminant", {}, rootSuper, std::nullopt, {}, nullptr, "Test", {}});
        TypeId firstKind = arena.addType(ExternType{"FirstKind", {}, discriminant, std::nullopt, {}, nullptr, "Test", {}});
        TypeId secondKind = arena.addType(ExternType{"SecondKind", {}, discriminant, std::nullopt, {}, nullptr, "Test", {}});
        TypeId unrelatedKind = arena.addType(ExternType{"UnrelatedKind", {}, rootSuper, std::nullopt, {}, nullptr, "Test", {}});

        TypeId firstVariant = arena.addType(ExternType{"FirstVariant", {}, rootSuper, std::nullopt, {}, nullptr, "Test", {}});
        getMutable<ExternType>(firstVariant)->props = {{"Kind", Property::readonly(firstKind)}};
        TypeId secondVariant = arena.addType(ExternType{"SecondVariant", {}, rootSuper, std::nullopt, {}, nullptr, "Test", {}});
        getMutable<ExternType>(secondVariant)->props = {{"Kind", Property::readonly(secondKind)}};
        TypeId commonVariant = arena.addType(ExternType{"CommonVariant", {}, rootSuper, std::nullopt, {}, nullptr, "Test", {}});
        getMutable<ExternType>(commonVariant)->props = {{"Kind", Property::readonly(firstKind)}};

        TypeId broadVariant = arena.addType(ExternType{"BroadVariant", {}, rootSuper, std::nullopt, {}, nullptr, "Test", {}});
        getMutable<ExternType>(broadVariant)->props = {{"Kind", Property::readonly(discriminant)}};
        TypeId writableVariant = arena.addType(ExternType{"WritableVariant", {}, rootSuper, std::nullopt, {}, nullptr, "Test", {}});
        getMutable<ExternType>(writableVariant)->props = {{"Kind", Property::rw(firstKind)}};
        TypeId missingVariant = arena.addType(ExternType{"MissingVariant", {}, rootSuper, std::nullopt, {}, nullptr, "Test", {}});
        TypeId unknownVariant = arena.addType(ExternType{"UnknownVariant", {}, rootSuper, std::nullopt, {}, nullptr, "Test", {}});
        getMutable<ExternType>(unknownVariant)->props = {{"Kind", Property::readonly(f.builtinTypes->unknownType)}};
        TypeId recursiveVariant = arena.addType(ExternType{"RecursiveVariant", {}, rootSuper, std::nullopt, {}, nullptr, "Test", {}});
        getMutable<ExternType>(recursiveVariant)->props = {{"Kind", Property::readonly(recursiveVariant)}};

        TypeId eitherKind = arena.addType(UnionType{{firstKind, secondKind}});
        TypeId ambiguousVariant = arena.addType(ExternType{"AmbiguousVariant", {}, rootSuper, std::nullopt, {}, nullptr, "Test", {}});
        getMutable<ExternType>(ambiguousVariant)->props = {{"Kind", Property::readonly(eitherKind)}};

        scope->bindings[AstName{"firstKindValue"}] = Binding{firstKind};
        scope->bindings[AstName{"secondKindValue"}] = Binding{secondKind};
        scope->bindings[AstName{"unrelatedKindValue"}] = Binding{unrelatedKind};

        f.globals.globalScope->exportedTypeBindings["Discriminant"] = TypeFun{{}, discriminant};
        f.globals.globalScope->exportedTypeBindings["FirstKind"] = TypeFun{{}, firstKind};
        f.globals.globalScope->exportedTypeBindings["SecondKind"] = TypeFun{{}, secondKind};
        f.globals.globalScope->exportedTypeBindings["UnrelatedKind"] = TypeFun{{}, unrelatedKind};
        f.globals.globalScope->exportedTypeBindings["FirstVariant"] = TypeFun{{}, firstVariant};
        f.globals.globalScope->exportedTypeBindings["SecondVariant"] = TypeFun{{}, secondVariant};
        f.globals.globalScope->exportedTypeBindings["CommonVariant"] = TypeFun{{}, commonVariant};
        f.globals.globalScope->exportedTypeBindings["BroadVariant"] = TypeFun{{}, broadVariant};
        f.globals.globalScope->exportedTypeBindings["WritableVariant"] = TypeFun{{}, writableVariant};
        f.globals.globalScope->exportedTypeBindings["MissingVariant"] = TypeFun{{}, missingVariant};
        f.globals.globalScope->exportedTypeBindings["UnknownVariant"] = TypeFun{{}, unknownVariant};
        f.globals.globalScope->exportedTypeBindings["RecursiveVariant"] = TypeFun{{}, recursiveVariant};
        f.globals.globalScope->exportedTypeBindings["AmbiguousVariant"] = TypeFun{{}, ambiguousVariant};

        f.globals.globalScope->exportedTypeBindings["Vector3"] = TypeFun{{}, vec3};
        f.globals.globalScope->exportedTypeBindings["Instance"] = TypeFun{{}, inst};
        f.globals.globalScope->exportedTypeBindings["ExternScriptConnection"] = TypeFun{{}, scriptConnection};
        f.globals.globalScope->exportedTypeBindings["Folder"] = TypeFun{{}, folder};
        f.globals.globalScope->exportedTypeBindings["Part"] = TypeFun{{}, part};
        f.globals.globalScope->exportedTypeBindings["WeldConstraint"] = TypeFun{{}, weldConstraint};

        for (const auto& [name, ty] : f.globals.globalScope->exportedTypeBindings)
            persist(ty.type);
        f.setLuauSolverMode(!FFlag::DebugLuauForceOldSolver ? SolverMode::New : SolverMode::Old);

        freeze(getFrontend().globals.globalTypes);
        return *frontend;
    }
};
} // namespace

TEST_SUITE_BEGIN("RefinementTest");

TEST_CASE_FIXTURE(Fixture, "is_truthy_constraint")
{
    CheckResult result = check(R"(
        function f(v: string?)
            if v then
                local s = v
            else
                local s = v
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("string", toString(requireTypeAtPosition({3, 26})));
    CHECK_EQ("nil", toString(requireTypeAtPosition({5, 26})));
}

TEST_CASE_FIXTURE(Fixture, "invert_is_truthy_constraint")
{
    CheckResult result = check(R"(
        function f(v: string?)
            if not v then
                local s = v
            else
                local s = v
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("nil", toString(requireTypeAtPosition({3, 26})));
    CHECK_EQ("string", toString(requireTypeAtPosition({5, 26})));
}

TEST_CASE_FIXTURE(Fixture, "parenthesized_expressions_are_followed_through")
{
    CheckResult result = check(R"(
        function f(v: string?)
            if (not v) then
                local s = v
            else
                local s = v
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("nil", toString(requireTypeAtPosition({3, 26})));
    CHECK_EQ("string", toString(requireTypeAtPosition({5, 26})));
}

TEST_CASE_FIXTURE(Fixture, "and_constraint")
{
    CheckResult result = check(R"(
        function f(a: string?, b: number?)
            if a and b then
                local x = a
                local y = b
            else
                local x = a
                local y = b
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("string", toString(requireTypeAtPosition({3, 26})));
    CHECK_EQ("number", toString(requireTypeAtPosition({4, 26})));

    CHECK_EQ("string?", toString(requireTypeAtPosition({6, 26})));
    CHECK_EQ("number?", toString(requireTypeAtPosition({7, 26})));
}

TEST_CASE_FIXTURE(Fixture, "not_and_constraint")
{
    CheckResult result = check(R"(
        function f(a: string?, b: number?)
            if not (a and b) then
                local x = a
                local y = b
            else
                local x = a
                local y = b
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("string?", toString(requireTypeAtPosition({3, 26})));
    CHECK_EQ("number?", toString(requireTypeAtPosition({4, 26})));

    CHECK_EQ("string", toString(requireTypeAtPosition({6, 26})));
    CHECK_EQ("number", toString(requireTypeAtPosition({7, 26})));
}

TEST_CASE_FIXTURE(Fixture, "or_predicate_with_truthy_predicates")
{
    CheckResult result = check(R"(
        function f(a: string?, b: number?)
            if a or b then
                local x = a
                local y = b
            else
                local x = a
                local y = b
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("string?", toString(requireTypeAtPosition({3, 26})));
    CHECK_EQ("number?", toString(requireTypeAtPosition({4, 26})));

    CHECK_EQ("nil", toString(requireTypeAtPosition({6, 26})));
    CHECK_EQ("nil", toString(requireTypeAtPosition({7, 26})));
}

TEST_CASE_FIXTURE(Fixture, "a_and_b_or_a_and_c")
{
    CheckResult result = check(R"(
        function f(a: string?, b: number?, c: boolean)
            if (a and b) or (a and c) then
                local foo = a
                local bar = b
                local baz = c
            else
                local foo = a
                local bar = b
                local baz = c
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);


    CHECK_EQ("string", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("number?", toString(requireTypeAtPosition({4, 28})));
    if (!FFlag::DebugLuauForceOldSolver)
        CHECK_EQ("boolean", toString(requireTypeAtPosition({5, 28})));
    else
        CHECK_EQ("true", toString(requireTypeAtPosition({5, 28}))); // oh no! :(

    CHECK_EQ("string?", toString(requireTypeAtPosition({7, 28})));
    CHECK_EQ("number?", toString(requireTypeAtPosition({8, 28})));
    CHECK_EQ("boolean", toString(requireTypeAtPosition({9, 28})));
}

TEST_CASE_FIXTURE(Fixture, "type_assertion_expr_carry_its_constraints")
{
    CheckResult result = check(R"(
        function g(a: number?, b: string?)
            if (a :: any) and (b :: any) then
                local x = a
                local y = b
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
    {
        CHECK_EQ("number?", toString(requireTypeAtPosition({3, 26})));
        CHECK_EQ("string?", toString(requireTypeAtPosition({4, 26})));
    }
    else
    {
        // We're going to drop support for type refinements through type assertions.
        CHECK_EQ("number", toString(requireTypeAtPosition({3, 26})));
        CHECK_EQ("string", toString(requireTypeAtPosition({4, 26})));
    }
}

TEST_CASE_FIXTURE(BuiltinsFixture, "typeguard_in_if_condition_position")
{
    CheckResult result = check(R"(
        function f(s: any, t: unknown)
            if type(s) == "number" then
                local n = s
            end
            if type(t) == "number" then
                local n = t
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    // DCR changes refinements to preserve error suppression.
    if (!FFlag::DebugLuauForceOldSolver)
        CHECK_EQ("*error-type* | number", toString(requireTypeAtPosition({3, 26})));
    else
        CHECK_EQ("number", toString(requireTypeAtPosition({3, 26})));
    CHECK_EQ("number", toString(requireTypeAtPosition({6, 26})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "typeguard_in_assert_position")
{
    CheckResult result = check(R"(
        function f(a)
            assert(type(a) == "number")
            local b = a
            return b
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
        CHECK("<a>(a) -> a & number" == toString(requireType("f")));
    else
        CHECK("<a>(a) -> number" == toString(requireType("f")));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refine_unknown_to_table_then_test_a_prop")
{
    CheckResult result = check(R"(
        local function f(x: unknown): string?
            if typeof(x) == "table" then
                if typeof(x.foo) == "string" then
                    return x.foo
                end
            end

            return nil
        end
    )");

    if (!FFlag::DebugLuauForceOldSolver)
        LUAU_REQUIRE_NO_ERRORS(result);
    else
    {
        LUAU_REQUIRE_ERROR_COUNT(2, result);

        for (size_t i = 0; i < result.errors.size(); i++)
        {
            const UnknownProperty* up = get<UnknownProperty>(result.errors[i]);
            REQUIRE_EQ("foo", up->key);
            REQUIRE_EQ("unknown", toString(up->table));
        }
    }
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refine_unknown_to_table_then_test_a_nested_prop")
{
    CheckResult result = check(R"(
        local function f(x: unknown): string?
            if typeof(x) == "table" then
                -- this should error, `x.foo` is an unknown property
                if typeof(x.foo.bar) == "string" then
                    return x.foo.bar
                end
            end

            return nil
        end
    )");

    if (!FFlag::DebugLuauForceOldSolver)
    {
        LUAU_REQUIRE_ERROR_COUNT(1, result);
        const UnknownProperty* up = get<UnknownProperty>(result.errors[0]);
        REQUIRE_EQ("bar", up->key);
        REQUIRE_EQ("unknown", toString(up->table));
    }
    else
    {
        LUAU_REQUIRE_ERROR_COUNT(2, result);

        for (size_t i = 0; i < result.errors.size(); i++)
        {
            const UnknownProperty* up = get<UnknownProperty>(result.errors[i]);
            REQUIRE_EQ("foo", up->key);
            REQUIRE_EQ("unknown", toString(up->table));
        }
    }
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refine_unknown_to_table_then_test_a_tested_nested_prop")
{
    CheckResult result = check(R"(
        local function f(x: unknown): string?
            if typeof(x) == "table" then
                if typeof(x.foo) == "table" and typeof(x.foo.bar) == "string" then
                    return x.foo.bar
                end
            end

            return nil
        end
    )");

    if (!FFlag::DebugLuauForceOldSolver)
        LUAU_REQUIRE_NO_ERRORS(result);
    else
    {
        LUAU_REQUIRE_ERROR_COUNT(3, result);

        for (size_t i = 0; i < result.errors.size(); i++)
        {
            const UnknownProperty* up = get<UnknownProperty>(result.errors[i]);
            REQUIRE_EQ("foo", up->key);
            REQUIRE_EQ("unknown", toString(up->table));
        }
    }
}

TEST_CASE_FIXTURE(BuiltinsFixture, "call_to_undefined_method_is_not_a_refinement")
{
    ScopedFastFlag sff[] = {
        {FFlag::DebugLuauForceOldSolver, false},
    };

    CheckResult result = check(R"(
        local function f(x: unknown)
            if typeof(x) == "table" then
                if x.foo() then
                end
            end
            return (nil :: never)
        end
    )");

    LUAU_REQUIRE_ERROR_COUNT(1, result);

    auto unknownProp = get<UnknownProperty>(result.errors[0]);
    REQUIRE_MESSAGE(unknownProp, "Expected UnknownProperty but got " << result.errors[0]);
    CHECK("foo" == unknownProp->key);
    CHECK("table" == toString(unknownProp->table));

    CHECK(Position{3, 19} == result.errors[0].location.begin);
    CHECK(Position{3, 24} == result.errors[0].location.end);
}

TEST_CASE_FIXTURE(BuiltinsFixture, "call_an_incompatible_function_after_using_typeguard")
{
    CheckResult result = check(R"(
        local function f(x: number)
            return x
        end

        local function g(x: unknown)
            if type(x) == "string" then
                f(x)
            end
        end

        local function h(x: any)
            if type(x) == "string" then
                f(x)
            end
        end
    )");

    if (!FFlag::DebugLuauForceOldSolver)
    {
        LUAU_REQUIRE_ERROR_COUNT(1, result);

        CHECK("Expected this to be 'number', but got 'string'" == toString(result.errors[0]));
        CHECK(Location{{7, 18}, {7, 19}} == result.errors[0].location);
    }
    else
    {
        LUAU_REQUIRE_ERROR_COUNT(2, result);

        CHECK("Expected this to be 'number', but got 'string'" == toString(result.errors[0]));
        CHECK(Location{{7, 18}, {7, 19}} == result.errors[0].location);

        CHECK("Expected this to be 'number', but got 'string'" == toString(result.errors[1]));
        CHECK(Location{{13, 18}, {13, 19}} == result.errors[1].location);
    }
}

TEST_CASE_FIXTURE(BuiltinsFixture, "impossible_type_narrow_is_not_an_error")
{
    // This unit test serves as a reminder to not implement this warning until Luau is intelligent enough.
    // For instance, getting a value out of the indexer and checking whether the value exists is not an error.
    CheckResult result = check(R"(
        local t: {string} = {"a", "b", "c"}
        local v = t[4]
        if not v then
            t[4] = "d"
        else
            print(v)
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(Fixture, "truthy_constraint_on_properties")
{
    CheckResult result = check(R"(
        local t: {x: number?} = {x = 1}

        if t.x then
            local t2 = t
            local foo = t.x
        end

        local bar = t.x
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
    {
        CHECK("{ read x: number, write x: number? }" == toString(requireTypeAtPosition({4, 23})));
        CHECK("number" == toString(requireTypeAtPosition({5, 26})));
    }

    CHECK_EQ("number?", toString(requireType("bar")));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "index_on_a_refined_property")
{
    CheckResult result = check(R"(
        local t: {x: {y: string}?} = {x = {y = "hello!"}}

        if t.x then
            print(t.x.y)
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(BuiltinsFixture, "assert_non_binary_expressions_actually_resolve_constraints")
{
    CheckResult result = check(R"(
        local foo: string? = "hello"
        assert(foo)
        local bar: string = foo
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(Fixture, "lvalue_is_equal_to_another_lvalue")
{
    CheckResult result = check(R"(
        local function f(a: (string | number)?, b: boolean?)
            if a == b then
                local foo, bar = a, b
            else
                local foo, bar = a, b
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ(toString(requireTypeAtPosition({3, 33})), "(number | string)?"); // a == b
    CHECK_EQ(toString(requireTypeAtPosition({3, 36})), "boolean?");           // a == b

    CHECK_EQ(toString(requireTypeAtPosition({5, 33})), "(number | string)?"); // a ~= b
    CHECK_EQ(toString(requireTypeAtPosition({5, 36})), "boolean?");           // a ~= b
}

TEST_CASE_FIXTURE(Fixture, "lvalue_is_equal_to_a_term")
{
    CheckResult result = check(R"(
        local function f(a: (string | number)?)
            if a == 1 then
                local foo = a
            else
                local foo = a
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ(toString(requireTypeAtPosition({3, 28})), "(number | string)?"); // a == 1;
    CHECK_EQ(toString(requireTypeAtPosition({5, 28})), "(number | string)?"); // a ~= 1
}

TEST_CASE_FIXTURE(Fixture, "term_is_equal_to_an_lvalue")
{
    CheckResult result = check(R"(
        local function f(a: (string | number)?)
            if "hello" == a then
                local foo = a
            else
                local foo = a
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
    {
        CHECK_EQ(toString(requireTypeAtPosition({3, 28})), R"("hello")");                         // a == "hello"
        CHECK_EQ(toString(requireTypeAtPosition({5, 28})), R"(((string & ~"hello") | number)?)"); // a ~= "hello"
    }
    else
    {
        CHECK_EQ(toString(requireTypeAtPosition({3, 28})), R"("hello")");            // a == "hello"
        CHECK_EQ(toString(requireTypeAtPosition({5, 28})), R"((number | string)?)"); // a ~= "hello"
    }
}

TEST_CASE_FIXTURE(Fixture, "lvalue_is_not_nil")
{
    CheckResult result = check(R"(
        local function f(a: (string | number)?)
            if a ~= nil then
                local foo = a
            else
                local foo = a
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ(toString(requireTypeAtPosition({3, 28})), "number | string"); // a ~= nil
    if (!FFlag::DebugLuauForceOldSolver)
        CHECK_EQ(toString(requireTypeAtPosition({5, 28})), "nil"); // a == nil :)
    else
        CHECK_EQ(toString(requireTypeAtPosition({5, 28})), "(number | string)?"); // a == nil
}

TEST_CASE_FIXTURE(Fixture, "free_type_is_equal_to_an_lvalue")
{
    CheckResult result = check(R"(
        local function f(a, b: string?)
            if a == b then
                local foo, bar = a, b
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
    {
        CHECK(toString(requireTypeAtPosition({3, 33})) == "unknown"); // a == b

        // FIXME: This type either comes out as string? or (string?) & unknown
        // depending on which tests are run and in which order. I'm not sure
        // where the nondeterminism is coming from.
        TypeArena arena;
        UnifierSharedState state{NotNull{&getFrontend().iceHandler}};
        Normalizer normalizer{&arena, getBuiltins(), NotNull{&state}, SolverMode::New};
        auto a = normalizer.normalize(requireTypeAtPosition({3, 36}));
        CHECK(toString(normalizer.typeFromNormal(*a)) == "string?"); // a == b
    }
    else
    {
        CHECK_EQ(toString(requireTypeAtPosition({3, 33})), "a");       // a == b
        CHECK_EQ(toString(requireTypeAtPosition({3, 36})), "string?"); // a == b
    }
}

TEST_CASE_FIXTURE(Fixture, "unknown_lvalue_is_not_synonymous_with_other_on_not_equal")
{
    CheckResult result = check(R"(
        local function f(a: any, b: {x: number}?)
            if a ~= b then
                local foo, bar = a, b
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ(toString(requireTypeAtPosition({3, 33})), "any");            // a ~= b
    CHECK_EQ(toString(requireTypeAtPosition({3, 36})), "{ x: number }?"); // a ~= b
}

TEST_CASE_FIXTURE(Fixture, "string_not_equal_to_string_or_nil")
{
    CheckResult result = check(R"(
        local t: {string} = {"hello"}

        local a: string = t[1]
        local b: string? = nil
        if a ~= b then
            local foo, bar = a, b
        else
            local foo, bar = a, b
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ(toString(requireTypeAtPosition({6, 29})), "string");  // a ~= b
    CHECK_EQ(toString(requireTypeAtPosition({6, 32})), "string?"); // a ~= b

    CHECK_EQ(toString(requireTypeAtPosition({8, 29})), "string");  // a == b
    CHECK_EQ(toString(requireTypeAtPosition({8, 32})), "string?"); // a == b
}

TEST_CASE_FIXTURE(Fixture, "narrow_property_of_a_bounded_variable")
{
    CheckResult result = check(R"(
        local t
        local u: {x: number?} = {x = nil}
        t = u

        if t.x then
            local foo: number = t.x
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(BuiltinsFixture, "type_narrow_to_vector")
{
    CheckResult result = check(R"(
        local function f(x)
            if type(x) == "vector" then
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
        CHECK_EQ("unknown & vector", toString(requireTypeAtPosition({3, 28})));
    else
        CHECK_EQ("*error-type*", toString(requireTypeAtPosition({3, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "nonoptional_type_can_narrow_to_nil_if_sense_is_true")
{
    ScopedFastFlag sffs[] = {
        {FFlag::DebugLuauAssertOnForcedConstraint, true},
        {FFlag::LuauRemovePrimitiveTypeConstraintAndSubtypingUnifier, true},
    };

    CheckResult result = check(R"(
        local t = {"hello"}
        local v = t[2]
        if type(v) == "nil" then
            local foo = v
        else
            local foo = v
        end

        if not (type(v) ~= "nil") then
            local foo = v
        else
            local foo = v
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
    {
        CHECK("nil & string" == toString(requireTypeAtPosition({4, 24})));  // type(v) == "nil"
        CHECK("string & ~nil" == toString(requireTypeAtPosition({6, 24}))); // type(v) ~= "nil"
    }
    else
    {
        CHECK_EQ("nil", toString(requireTypeAtPosition({4, 24})));    // type(v) == "nil"
        CHECK_EQ("string", toString(requireTypeAtPosition({6, 24}))); // type(v) ~= "nil"
    }

    CHECK_EQ("nil", toString(requireTypeAtPosition({10, 24})));    // equivalent to type(v) == "nil"
    CHECK_EQ("string", toString(requireTypeAtPosition({12, 24}))); // equivalent to type(v) ~= "nil"
}

TEST_CASE_FIXTURE(BuiltinsFixture, "typeguard_not_to_be_string")
{
    CheckResult result = check(R"(
        local function f(x: string | number | boolean)
            if type(x) ~= "string" then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("boolean | number", toString(requireTypeAtPosition({3, 28}))); // type(x) ~= "string"
    CHECK_EQ("string", toString(requireTypeAtPosition({5, 28})));           // type(x) == "string"
}

TEST_CASE_FIXTURE(BuiltinsFixture, "typeguard_narrows_for_table")
{
    CheckResult result = check(R"(
        local function f(x: string | {x: number} | {y: boolean})
            if type(x) == "table" then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("{ x: number } | { y: boolean }", toString(requireTypeAtPosition({3, 28}))); // type(x) == "table"
    CHECK_EQ("string", toString(requireTypeAtPosition({5, 28})));                         // type(x) ~= "table"
}

TEST_CASE_FIXTURE(BuiltinsFixture, "typeguard_narrows_for_functions")
{
    CheckResult result = check(R"(
        local function weird(x: string | ((number) -> string))
            if type(x) == "function" then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("(number) -> string", toString(requireTypeAtPosition({3, 28}))); // type(x) == "function"
    CHECK_EQ("string", toString(requireTypeAtPosition({5, 28})));             // type(x) ~= "function"
}

TEST_CASE_FIXTURE(BuiltinsFixture, "type_guard_can_filter_for_intersection_of_tables")
{
    CheckResult result = check(R"(
        type XYCoord = {x: number} & {y: number}
        local function f(t: XYCoord?)
            if type(t) == "table" then
                local foo = t
            else
                local foo = t
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    ToStringOptions opts;
    opts.exhaustive = true;
    CHECK_EQ("{ x: number } & { y: number }", toString(requireTypeAtPosition({4, 28}), opts));
    CHECK_EQ("nil", toString(requireTypeAtPosition({6, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "type_guard_can_filter_for_overloaded_function")
{
    CheckResult result = check(R"(
        type SomeOverloadedFunction = ((number) -> string) & ((string) -> number)
        local function f(g: SomeOverloadedFunction?)
            if type(g) == "function" then
                local foo = g
            else
                local foo = g
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("((number) -> string) & ((string) -> number)", toString(requireTypeAtPosition({4, 28})));
    CHECK_EQ("nil", toString(requireTypeAtPosition({6, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "type_guard_narrowed_into_nothingness")
{
    CheckResult result = check(R"(
        local function f(t: {x: number})
            if type(t) ~= "table" then
                local foo = t
                error(("Expected a table, got %s"):format(type(t)))
            end

            return t.x + 1
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
    {
        // CLI-115281 Types produced by refinements do not consistently get simplified
        CHECK_EQ("{ x: number } & ~table", toString(requireTypeAtPosition({3, 28})));
    }
    else
        CHECK_EQ("never", toString(requireTypeAtPosition({3, 28})));
}

TEST_CASE_FIXTURE(Fixture, "not_a_or_not_b")
{
    CheckResult result = check(R"(
        local function f(a: number?, b: number?)
            if (not a) or (not b) then
                local foo = a
                local bar = b
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("number?", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("number?", toString(requireTypeAtPosition({4, 28})));
}

TEST_CASE_FIXTURE(Fixture, "not_a_or_not_b2")
{
    CheckResult result = check(R"(
        local function f(a: number?, b: number?)
            if not (a and b) then
                local foo = a
                local bar = b
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("number?", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("number?", toString(requireTypeAtPosition({4, 28})));
}

TEST_CASE_FIXTURE(Fixture, "not_a_and_not_b")
{
    CheckResult result = check(R"(
        local function f(a: number?, b: number?)
            if (not a) and (not b) then
                local foo = a
                local bar = b
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("nil", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("nil", toString(requireTypeAtPosition({4, 28})));
}

TEST_CASE_FIXTURE(Fixture, "not_a_and_not_b2")
{
    CheckResult result = check(R"(
        local function f(a: number?, b: number?)
            if not (a or b) then
                local foo = a
                local bar = b
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("nil", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("nil", toString(requireTypeAtPosition({4, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "either_number_or_string")
{
    CheckResult result = check(R"(
        local function f(x: any, y: unknown)
            if type(x) == "number" or type(x) == "string" then
                local foo = x
            end
            if type(y) == "number" or type(y) == "string" then
                local foo = y
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
        CHECK_EQ("*error-type* | number | string", toString(requireTypeAtPosition({3, 28})));
    else
        CHECK_EQ("number | string", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("number | string", toString(requireTypeAtPosition({6, 28})));
}

TEST_CASE_FIXTURE(Fixture, "not_t_or_some_prop_of_t")
{
    CheckResult result = check(R"(
        local function f(t: {x: boolean}?)
            if not t or t.x then
                local foo = t
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
    {
        // CLI-115281 Types produced by refinements do not consistently get simplified: we are minting a type like:
        //
        //  intersect<{ x: boolean } | nil, { read x: ~(false?) } | false | nil>
        //
        // ... which we can't _quite_ refine into the type it ought to be:
        //
        //  { write x: boolean, read x: true } | nil
        CHECK_EQ("({ read x: ~(false?) } & { x: boolean })?", toString(requireTypeAtPosition({3, 28})));
    }
    else
        CHECK_EQ("{ x: boolean }?", toString(requireTypeAtPosition({3, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "assert_a_to_be_truthy_then_assert_a_to_be_number")
{
    CheckResult result = check(R"(
        local a: (number | string)?
        assert(a)
        local b = a
        assert(type(a) == "number")
        local c = a
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("number | string", toString(requireTypeAtPosition({3, 18})));
    CHECK_EQ("number", toString(requireTypeAtPosition({5, 18})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "merge_should_be_fully_agnostic_of_hashmap_ordering")
{
    // This bug came up because there was a mistake in Luau::merge where zipping on two maps would produce the wrong merged result.
    CheckResult result = check(R"(
        local function f(b: string | { x: string }, a)
            assert(type(a) == "string")
            assert(type(b) == "string" or type(b) == "table")

            if type(b) == "string" then
                local foo = b
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("string", toString(requireTypeAtPosition({6, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refine_the_correct_types_opposite_of_when_a_is_not_number_or_string")
{
    CheckResult result = check(R"(
        local function f(a: string | number | boolean)
            if type(a) ~= "number" and type(a) ~= "string" then
                local foo = a
            else
                local foo = a
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("boolean", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("number | string", toString(requireTypeAtPosition({5, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "is_truthy_constraint_ifelse_expression")
{
    CheckResult result = check(R"(
        function f(v:string?)
            return if v then v else tostring(v)
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("string", toString(requireTypeAtPosition({2, 29})));
    CHECK_EQ("nil", toString(requireTypeAtPosition({2, 45})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "invert_is_truthy_constraint_ifelse_expression")
{
    CheckResult result = check(R"(
        function f(v:string?)
            return if not v then tostring(v) else v
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("nil", toString(requireTypeAtPosition({2, 42})));
    CHECK_EQ("string", toString(requireTypeAtPosition({2, 50})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "type_comparison_ifelse_expression")
{
    CheckResult result = check(R"(
        function returnOne(x)
            return 1
        end

        function f(v:any)
            return if typeof(v) == "number" then v else returnOne(v)
        end

        function g(v:unknown)
            return if typeof(v) == "number" then v else returnOne(v)
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
    {
        CHECK_EQ("*error-type* | number", toString(requireTypeAtPosition({6, 49})));
        CHECK_EQ("*error-type* | ~number", toString(requireTypeAtPosition({6, 66})));
    }
    else
    {
        CHECK_EQ("number", toString(requireTypeAtPosition({6, 49})));
        CHECK_EQ("any", toString(requireTypeAtPosition({6, 66})));
    }

    CHECK_EQ("number", toString(requireTypeAtPosition({10, 49})));
    if (!FFlag::DebugLuauForceOldSolver)
        CHECK_EQ("~number", toString(requireTypeAtPosition({10, 66})));
    else
        CHECK_EQ("unknown", toString(requireTypeAtPosition({10, 66})));
}


TEST_CASE_FIXTURE(BuiltinsFixture, "is_truthy_constraint_while_expression")
{
    CheckResult result = check(R"(
        function f(v:string?)
            while v do
                local foo = v
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("string", toString(requireTypeAtPosition({3, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "invert_is_truthy_constraint_while_expression")
{
    CheckResult result = check(R"(
        function f(v:string?)
            while not v do
                local foo = v
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("nil", toString(requireTypeAtPosition({3, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refine_the_correct_types_opposite_of_while_a_is_not_number_or_string")
{
    CheckResult result = check(R"(
        local function f(a: string | number | boolean)
            while type(a) ~= "number" and type(a) ~= "string" do
                local foo = a
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("boolean", toString(requireTypeAtPosition({3, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "correctly_lookup_a_shadowed_local_that_which_was_previously_refined")
{
    CheckResult result = check(R"(
        local foo: string? = "hi"
        assert(foo)
        local foo: number = 5
        print(foo:sub(1, 1))
    )");

    LUAU_REQUIRE_ERROR_COUNT(1, result);

    CHECK_EQ("Type 'number' does not have key 'sub'", toString(result.errors[0]));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "correctly_lookup_property_whose_base_was_previously_refined")
{
    CheckResult result = check(R"(
        type T = {x: string | number}
        local t: T? = {x = "hi"}
        if t then
            if type(t.x) == "string" then
                local foo = t.x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("string", toString(requireTypeAtPosition({5, 30})));
}

TEST_CASE_FIXTURE(Fixture, "correctly_lookup_property_whose_base_was_previously_refined2")
{
    CheckResult result = check(R"(
        type T = { x: { y: number }? }

        local function f(t: T?)
            if t and t.x then
                local foo = t.x.y
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("number", toString(requireTypeAtPosition({5, 32})));
}

TEST_CASE_FIXTURE(Fixture, "apply_refinements_on_astexprindexexpr_whose_subscript_expr_is_constant_string")
{
    CheckResult result = check(R"(
        type T = { [string]: { prop: number }? }
        local t: T = {}

        if t["hello"] then
            local foo = t["hello"].prop
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(Fixture, "discriminate_from_truthiness_of_x")
{
    CheckResult result = check(R"(
        type T = {tag: "missing", x: nil} | {tag: "exists", x: string}

        local function f(t: T)
            if t.x then
                local foo = t
            else
                local bar = t
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
    {
        CHECK(R"({ tag: "exists", x: string })" == toString(requireTypeAtPosition({5, 28})));
        CHECK(R"({ tag: "missing", x: nil })" == toString(requireTypeAtPosition({7, 28})));
    }
    else
    {
        CHECK_EQ(R"({ tag: "exists", x: string })", toString(requireTypeAtPosition({5, 28})));
        CHECK_EQ(R"({ tag: "exists", x: string } | { tag: "missing", x: nil })", toString(requireTypeAtPosition({7, 28})));
    }
}

TEST_CASE_FIXTURE(Fixture, "discriminate_tag")
{
    CheckResult result = check(R"(
        type Cat = {tag: "Cat", name: string, catfood: string}
        type Dog = {tag: "Dog", name: string, dogfood: string}
        type Animal = Cat | Dog

        local function f(animal: Animal)
            if animal.tag == "Cat" then
                local cat = animal
            elseif animal.tag == "Dog" then
                local dog = animal
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("Cat", toString(requireTypeAtPosition({7, 33})));
    CHECK_EQ("Dog", toString(requireTypeAtPosition({9, 33})));
}

TEST_CASE_FIXTURE(Fixture, "discriminate_tag_with_implicit_else")
{
    CheckResult result = check(R"(
        type Cat = {tag: "Cat", name: string, catfood: string}
        type Dog = {tag: "Dog", name: string, dogfood: string}
        type Animal = Cat | Dog

        local function f(animal: Animal)
            if animal.tag == "Cat" then
                local cat = animal
            else
                local dog = animal
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("Cat", toString(requireTypeAtPosition({7, 33})));
    CHECK_EQ("Dog", toString(requireTypeAtPosition({9, 33})));
}

TEST_CASE_FIXTURE(Fixture, "and_or_peephole_refinement")
{
    CheckResult result = check(R"(
        local function len(a: {any})
            return a and #a or nil
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(Fixture, "narrow_boolean_to_true_or_false")
{
    CheckResult result = check(R"(
        local function f(x: boolean)
            if x then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("true", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("false", toString(requireTypeAtPosition({5, 28})));
}

TEST_CASE_FIXTURE(Fixture, "discriminate_on_properties_of_disjoint_tables_where_that_property_is_true_or_false")
{
    CheckResult result = check(R"(
        type Ok<T> = { ok: true, value: T }
        type Err<E> = { ok: false, error: E }
        type Result<T, E> = Ok<T> | Err<E>

        local function apply<T, E>(t: Result<T, E>, f: (T) -> (), g: (E) -> ())
            if t.ok then
                f(t.value)
            else
                g(t.error)
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(Fixture, "refine_a_property_not_to_be_nil_through_an_intersection_table")
{
    CheckResult result = check(R"(
        type T = {} & {f: ((string) -> string)?}
        local function f(t: T, x)
            if t.f then
                t.f(x)
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "discriminate_from_isa_of_x")
{
    CheckResult result = check(R"(
        type T = {tag: "Part", x: Part} | {tag: "Folder", x: Folder}

        local function f(t: T)
            if t.x:IsA("Part") then
                local foo = t
            else
                local bar = t
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);


    CHECK(R"({ tag: "Part", x: Part })" == toString(requireTypeAtPosition({5, 28})));
    CHECK(R"({ tag: "Folder", x: Folder })" == toString(requireTypeAtPosition({7, 28})));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "typeguard_cast_free_table_to_vector")
{
    // CLI-115286 - Refining via type(x) == 'vector' does not work in the new solver
    DOES_NOT_PASS_NEW_SOLVER_GUARD();
    getFrontend().setLuauSolverMode(!FFlag::DebugLuauForceOldSolver ? SolverMode::New : SolverMode::Old);
    CheckResult result = check(R"(
        local function f(vec)
            local X, Y, Z = vec.X, vec.Y, vec.Z

            if type(vec) == "vector" then
                local foo = vec
            elseif typeof(vec) == "Instance" then
                local foo = vec
            else
                local foo = vec
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("Vector3", toString(requireTypeAtPosition({5, 28}))); // type(vec) == "vector"

    CHECK_EQ("never", toString(requireTypeAtPosition({7, 28}))); // typeof(vec) == "Instance"

    CHECK_EQ("{+ X: a, Y: b, Z: c +}", toString(requireTypeAtPosition({9, 28}))); // type(vec) ~= "vector" and typeof(vec) ~= "Instance"
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "typeguard_cast_instance_or_vector3_to_vector")
{
    CheckResult result = check(R"(
        local function f(x: Instance | Vector3)
            if typeof(x) == "Vector3" then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("Vector3", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("Instance", toString(requireTypeAtPosition({5, 28})));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "type_narrow_for_all_the_userdata")
{
    CheckResult result = check(R"(
        local function f(x: string | number | Instance | Vector3)
            if type(x) == "userdata" then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("Instance | Vector3", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("number | string", toString(requireTypeAtPosition({5, 28})));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "type_narrow_but_the_discriminant_type_isnt_a_class")
{
    CheckResult result = check(R"(
        local function f(x: string | number | Instance | Vector3)
            if type(x) == "any" then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
    {
        CHECK_EQ("never", toString(requireTypeAtPosition({3, 28})));
        CHECK_EQ("Instance | Vector3 | number | string", toString(requireTypeAtPosition({5, 28})));
    }
    else
    {
        CHECK_EQ("*error-type*", toString(requireTypeAtPosition({3, 28})));
        CHECK_EQ("*error-type*", toString(requireTypeAtPosition({5, 28})));
    }
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "eliminate_subclasses_of_instance")
{
    CheckResult result = check(R"(
        local function f(x: Part | Folder | string)
            if typeof(x) == "Instance" then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("Folder | Part", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("string", toString(requireTypeAtPosition({5, 28})));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "narrow_from_subclasses_of_instance_or_string_or_vector3")
{
    CheckResult result = check(R"(
        local function f(x: Part | Folder | string | Vector3)
            if typeof(x) == "Instance" then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("Folder | Part", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("Vector3 | string", toString(requireTypeAtPosition({5, 28})));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "x_as_any_if_x_is_instance_elseif_x_is_table")
{
    // CLI-117136 - this code doesn't finish constraint solving and has blocked types in the output
    if (!FFlag::DebugLuauForceOldSolver)
        return;
    CheckResult result = check(R"(
        --!nonstrict

        local function f(x)
            if typeof(x) == "Instance" and x:IsA("Folder") then
                local foo = x
            elseif typeof(x) == "table" then
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
    {
        CHECK_EQ("Folder & Instance & {-  -}", toString(requireTypeAtPosition({5, 28})));
        CHECK_EQ("(~Folder | ~Instance) & {-  -} & never", toString(requireTypeAtPosition({7, 28})));
    }
    else
    {
        CHECK_EQ("Folder", toString(requireTypeAtPosition({5, 28})));
        CHECK_EQ("any", toString(requireTypeAtPosition({7, 28})));
    }
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "refine_param_of_type_instance_without_using_typeof")
{
    CheckResult result = check(R"(
        local function f(x: Instance)
            if x:IsA("Folder") then
                local foo = x
            elseif typeof(x) == "table" then
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("Folder", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("never", toString(requireTypeAtPosition({5, 28})));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "refine_param_of_type_folder_or_part_without_using_typeof")
{
    CheckResult result = check(R"(
        local function f(x: Part | Folder)
            if x:IsA("Folder") then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("Folder", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("Part", toString(requireTypeAtPosition({5, 28})));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "isa_type_refinement_must_be_known_ahead_of_time")
{
    CheckResult result = check(R"(
        local function f(x): Instance
            if x:IsA("Folder") then
                local foo = x
            else
                local foo = x
            end

            return x
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
    {
        CHECK_EQ("t1 where t1 = Instance & { read IsA: (t1, string) -> (unknown, ...unknown) }", toString(requireTypeAtPosition({3, 28})));
        CHECK_EQ("t1 where t1 = Instance & { read IsA: (t1, string) -> (unknown, ...unknown) }", toString(requireTypeAtPosition({5, 28})));
    }
    else
    {
        CHECK_EQ("Instance", toString(requireTypeAtPosition({3, 28})));
        CHECK_EQ("Instance", toString(requireTypeAtPosition({5, 28})));
    }
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "asserting_optional_properties_should_not_refine_extern_types_to_never")
{

    CheckResult result = check(R"(
        local weld: WeldConstraint = nil :: any
        assert(weld.Part1)
        print(weld) -- hover type incorrectly becomes `never`
        assert(weld.Part1.Name == "RootPart")
        local part1 = assert(weld.Part1)
        local pos = part1.Position
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
        CHECK_EQ("WeldConstraint & { read Part1: ~(false?) }", toString(requireTypeAtPosition({3, 15})));
    else
        CHECK_EQ("WeldConstraint", toString(requireTypeAtPosition({3, 15})));
    CHECK_EQ("Vector3", toString(requireTypeAtPosition({6, 29})));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "asserting_non_existent_properties_should_not_refine_extern_types_to_never")
{
    ScopedFastFlag _{FFlag::LuauIndexingIntoErrorGivesError, true};

    CheckResult result = check(R"(
        local weld: WeldConstraint = nil :: any
        assert(weld.Part8)
        print(weld)
        assert(weld.Part8.Name == "RootPart")
        local part8 = assert(weld.Part8)
        local pos = part8.Position
    )");

    LUAU_REQUIRE_ERRORS(result);
    CHECK_EQ(toString(result.errors[0]), "Key 'Part8' not found in external type 'WeldConstraint'");

    CHECK_EQ("WeldConstraint", toString(requireTypeAtPosition({3, 15})));
    CHECK_EQ("*error-type*", toString(requireTypeAtPosition({6, 29})));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "x_is_not_instance_or_else_not_part")
{
    CheckResult result = check(R"(
        local function f(x: Part | Folder | string)
            if typeof(x) ~= "Instance" or not x:IsA("Part") then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("Folder | string", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("Part", toString(requireTypeAtPosition({5, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "typeguard_doesnt_leak_to_elseif")
{
    CheckResult result = check(R"(
        function f(a)
           if type(a) == "boolean" then
                local a1 = a
            elseif a.fn() then
                local a2 = a
            else
                local a3 = a
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refine_unknowns")
{
    CheckResult result = check(R"(
        local function f(x: unknown)
            if type(x) == "string" then
                local foo = x
            else
                local bar = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
    {
        CHECK_EQ("string", toString(requireTypeAtPosition({3, 28})));
        CHECK_EQ("~string", toString(requireTypeAtPosition({5, 28})));
    }
    else
    {
        CHECK_EQ("string", toString(requireTypeAtPosition({3, 28})));
        CHECK_EQ("unknown", toString(requireTypeAtPosition({5, 28})));
    }
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refine_boolean")
{
    CheckResult result = check(R"(
        local function f(x: number | boolean)
            if typeof(x) == "boolean" then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    CHECK_EQ("boolean", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("number", toString(requireTypeAtPosition({5, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refine_thread")
{
    CheckResult result = check(R"(
        local function f(x: number | thread)
            if typeof(x) == "thread" then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    CHECK_EQ("thread", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("number", toString(requireTypeAtPosition({5, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refine_buffer")
{
    CheckResult result = check(R"(
        local function f(x: number | buffer)
            if typeof(x) == "buffer" then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    CHECK_EQ("buffer", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("number", toString(requireTypeAtPosition({5, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "falsiness_of_TruthyPredicate_narrows_into_nil")
{
    CheckResult result = check(R"(
        local function f(t: {number})
            local x = t[1]
            if not x then
                local foo = x
            else
                local bar = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("nil", toString(requireTypeAtPosition({4, 28})));
    CHECK_EQ("number", toString(requireTypeAtPosition({6, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "what_nonsensical_condition")
{
    CheckResult result = check(R"(
        local function f(x)
            if type(x) == "string" and type(x) == "number" then
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("never", toString(requireTypeAtPosition({3, 28})));
}

TEST_CASE_FIXTURE(Fixture, "else_with_no_explicit_expression_should_also_refine_the_tagged_union")
{
    CheckResult result = check(R"(
        type Ok<T> = { tag: "ok", value: T }
        type Err<E> = { tag: "err", err: E }
        type Result<T, E> = Ok<T> | Err<E>

        function and_then<T, U, E>(r: Result<T, E>, f: (T) -> U): Result<U, E>
            if r.tag == "ok" then
                return { tag = "ok", value = f(r.value) }
            else
                return r
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(Fixture, "fuzz_filtered_refined_types_are_followed")
{
    CheckResult result = check(R"(
local _
do
local _ = _ ~= _ or _ or _
end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refine_unknown_to_table_then_take_the_length")
{
    CheckResult result = check(R"(
        local function f(x: unknown)
            if typeof(x) == "table" then
                local len = #x
            end
        end
    )");

    if (!FFlag::DebugLuauForceOldSolver)
    {
        LUAU_REQUIRE_NO_ERRORS(result);
        CHECK_EQ("table", toString(requireTypeAtPosition({3, 29})));
    }
    else
    {
        LUAU_REQUIRE_ERROR_COUNT(1, result);
        CHECK_EQ("unknown", toString(requireTypeAtPosition({3, 29})));
    }
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refine_unknown_to_table_then_clone_it")
{
    CheckResult result = check(R"(
        local function f(x: unknown)
            if typeof(x) == "table" then
                local cloned: {} = table.clone(x)
            end
        end
    )");

    if (!FFlag::DebugLuauForceOldSolver)
    {
        LUAU_REQUIRE_NO_ERRORS(result);
    }
    else
    {
        LUAU_REQUIRE_ERROR_COUNT(1, result);
    }
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "refine_a_param_that_got_resolved_during_constraint_solving_stage")
{
    CheckResult result = check(R"(
        type Id<T> = T

        local function f(x: Id<Id<Part | Folder> | Id<string>>)
            if typeof(x) ~= "string" and x:IsA("Part") then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    CHECK_EQ("Part", toString(requireTypeAtPosition({5, 28})));
    CHECK_EQ("Folder | string", toString(requireTypeAtPosition({7, 28})));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "refine_a_param_that_got_resolved_during_constraint_solving_stage_2")
{
    CheckResult result = check(R"(
        local function hof(f: (Instance) -> ()) end

        hof(function(inst)
            if inst:IsA("Part") then
                local foo = inst
            else
                local foo = inst
            end
        end)
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    CHECK_EQ("Part", toString(requireTypeAtPosition({5, 28})));
    if (!FFlag::DebugLuauForceOldSolver)
        CHECK_EQ("Instance & ~Part", toString(requireTypeAtPosition({7, 28})));
    else
        CHECK_EQ("Instance", toString(requireTypeAtPosition({7, 28})));
}

TEST_CASE_FIXTURE(Fixture, "refine_a_property_of_some_global")
{
    CheckResult result = check(R"(
        foo = { bar = 5 :: number? }

        if foo.bar then
            local bar = foo.bar
        end
    )");

    if (!FFlag::DebugLuauForceOldSolver)
    {
        LUAU_REQUIRE_ERROR_COUNT(1, result);
        CHECK_EQ("number", toString(requireTypeAtPosition({4, 30})));
    }
}

TEST_CASE_FIXTURE(BuiltinsFixture, "dataflow_analysis_can_tell_refinements_when_its_appropriate_to_refine_into_nil_or_never")
{
    CheckResult result = check(R"(
        local function f(t: {string}, s: string)
            local v1 = t[5]
            local v2 = v1

            if typeof(v1) == "nil" then
                local foo = v1
            else
                local foo = v1
            end

            if typeof(v2) == "nil" then
                local foo = v2
            else
                local foo = v2
            end

            if typeof(s) == "nil" then
                local foo = s -- line 18
            else
                local foo = s -- line 20
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("nil", toString(requireTypeAtPosition({6, 28})));
    CHECK_EQ("string", toString(requireTypeAtPosition({8, 28})));

    CHECK_EQ("nil", toString(requireTypeAtPosition({12, 28})));
    CHECK_EQ("string", toString(requireTypeAtPosition({14, 28})));

    if (!FFlag::DebugLuauForceOldSolver)
    {
        // CLI-115281 - Types produced by refinements don't always get simplified
        CHECK_EQ("nil & string", toString(requireTypeAtPosition({18, 28})));
        CHECK_EQ("string", toString(requireTypeAtPosition({20, 28})));
    }
    else
    {
        CHECK_EQ("nil", toString(requireTypeAtPosition({18, 28})));
        CHECK_EQ("string", toString(requireTypeAtPosition({20, 28})));
    }
}

TEST_CASE_FIXTURE(Fixture, "cat_or_dog_through_a_local")
{
    CheckResult result = check(R"(
        type Cat = { tag: "cat", catfood: string }
        type Dog = { tag: "dog", dogfood: string }
        type Animal = Cat | Dog

        local function f(animal: Animal)
            local tag = animal.tag
            if tag == "dog" then
                local dog = animal
            elseif tag == "cat" then
                local cat = animal
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("Cat | Dog", toString(requireTypeAtPosition({8, 28})));
    CHECK_EQ("Cat | Dog", toString(requireTypeAtPosition({10, 28})));
}

TEST_CASE_FIXTURE(Fixture, "locals_from_unstable_property_sources_refine_without_refining_the_source")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        --!strict

        type Alive = { rootPart: number }
        type State = { aliveState: Alive? }

        local function fromDynamicIndex(states: { [string]: State }, key: string): number?
            local aliveState = states[key].aliveState
            if aliveState == nil then
                return nil
            end
            return aliveState.rootPart
        end

        local function fromCall(getState: () -> State): number?
            local aliveState = getState().aliveState
            if aliveState == nil then
                return nil
            end
            return aliveState.rootPart
        end
    )"));

    CheckResult unstableSource = check(R"(
        --!strict

        type A = { read kind: "a", read aOnly: number }
        type B = { read kind: "b", read bOnly: number }
        type Variant = A | B

        local function read(values: { [string]: Variant }, key: string): number?
            local kind = values[key].kind
            if kind == "a" then
                return values[key].aOnly
            end
            return nil
        end
    )");

    LUAU_REQUIRE_ERROR_COUNT(1, unstableSource);
    CHECK(get<MissingUnionProperty>(unstableSource.errors[0]));
}

TEST_CASE_FIXTURE(Fixture, "readonly_property_discriminant_alias_refines_its_source")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        type A = { read kind: "a", read aOnly: number }
        type B = { read kind: "b", read bOnly: number }
        type Variant = A | B

        local function direct(value: Variant)
            if value.kind == "a" then
                local directResult = value
            end
        end

        local function throughAlias(value: Variant)
            local kind = value.kind
            if kind == "a" then
                local aliasResult = value
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    CHECK_EQ("A", toString(requireTypeAtPosition({7, 37})));
    CHECK_EQ("A", toString(requireTypeAtPosition({14, 36})));
}

TEST_CASE_FIXTURE(Fixture, "property_discriminant_alias_provenance_respects_compound_condition_evaluation_order")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        type A = { read kind: "a", read aOnly: number }
        type B = { read kind: "b", read bOnly: number }
        type Variant = A | B

        local function sideEffectFreeAnd(value: Variant, flag: boolean)
            local kind = value.kind
            if kind == "a" and flag then
                local sideEffectFreeAndResult = value
            end
        end

        local function sideEffectFreeNested(value: Variant, first: boolean, second: boolean)
            local kind = value.kind
            if (kind == "a" and first) or (kind == "a" and second) then
                local sideEffectFreeNestedResult = value
            end
        end

        local function laterCall(value: Variant, mutate: (Variant) -> boolean)
            local kind = value.kind
            if kind == "a" and mutate(value) then
                local afterLaterCall = value
            end
        end

        local function nestedLaterCall(value: Variant, mutate: (Variant) -> boolean, flag: boolean)
            local kind = value.kind
            if (kind == "a" and flag) and mutate(value) then
                local afterNestedLaterCall = value
            end
        end

        local function nestedOrLaterCall(value: Variant, mutate: (Variant) -> boolean)
            local kind = value.kind
            if (kind == "a" and mutate(value)) or false then
                local afterNestedOrLaterCall = value
            end
        end

        local function unaryLaterCall(value: Variant, mutate: (Variant) -> boolean)
            local kind = value.kind
            if not (kind ~= "a") and mutate(value) then
                local afterUnaryLaterCall = value
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    CHECK_EQ("A", toString(requireTypeAtPosition({8, 48})));
    // Both paths carry the property proof; collapsing this structural refinement to A is outside this regression's scope.
    CHECK_EQ(R"((A & { read kind: "a" | "a" }) | (B & { read kind: "a" | "a" }))", toString(requireTypeAtPosition({15, 51})));
    CHECK_EQ("A | B", toString(requireTypeAtPosition({22, 39})));
    CHECK_EQ("A | B", toString(requireTypeAtPosition({29, 45})));
    CHECK_EQ("A | B", toString(requireTypeAtPosition({36, 47})));
    CHECK_EQ("A | B", toString(requireTypeAtPosition({43, 44})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "readonly_extern_property_discriminant_alias_refines_its_source")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    loadDefinition(R"(
        declare extern type A with
            read kind: "a"
            read aOnly: number
        end

        declare extern type B with
            read kind: "b"
            read bOnly: number
        end
    )");

    CheckResult result = check(R"(
        local function direct(value: A | B)
            if value.kind == "a" then
                local directExternResult = value
            end
        end

        local function throughAlias(value: A | B)
            local kind = value.kind
            if kind == "a" then
                local aliasExternResult = value
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    CHECK_EQ("A", toString(requireTypeAtPosition({3, 43})));
    CHECK_EQ("A", toString(requireTypeAtPosition({10, 42})));
}

TEST_CASE_FIXTURE(Fixture, "property_discriminant_alias_provenance_is_conservatively_invalidated")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        type A = {
            read kind: "a",
            write kind: "a" | "b",
            read aOnly: number,
            [string]: unknown,
        }
        type B = {
            read kind: "b",
            write kind: "a" | "b",
            read bOnly: number,
            [string]: unknown,
        }
        type Variant = A | B

        local function reassignedAlias(value: Variant)
            local kind = value.kind
            kind = "a"
            if kind == "a" then
                local afterAliasReassignment = value
            end
        end

        local function writableSource(value: Variant)
            local kind = value.kind
            if kind == "a" then
                local fromWritableSource = value
            end
        end

        local function writtenSource(value: Variant)
            local kind = value.kind
            value.kind = "a"
            if kind == "a" then
                local afterSourceWrite = value
            end
        end

        local function dynamicWrite(value: Variant, key: string)
            local kind = value.kind
            value[key] = nil
            if kind == "a" then
                local afterDynamicWrite = value
            end
        end

        local function mutationCapableCall(value: Variant, mutate: (Variant) -> ())
            local kind = value.kind
            mutate(value)
            if kind == "a" then
                local afterMutationCapableCall = value
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    CHECK_EQ("A | B", toString(requireTypeAtPosition({19, 47})));
    CHECK_EQ("A | B", toString(requireTypeAtPosition({26, 43})));
    CHECK_EQ("A | B", toString(requireTypeAtPosition({34, 41})));
    CHECK_EQ("A | B", toString(requireTypeAtPosition({42, 42})));
    CHECK_EQ("A | B", toString(requireTypeAtPosition({50, 49})));
}

TEST_CASE_FIXTURE(Fixture, "property_discriminant_alias_provenance_is_versioned")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        type A = { read kind: "a", read aOnly: number }
        type B = { read kind: "b", read bOnly: number }
        type Variant = A | B

        local function aliasChain(value: Variant)
            local first = value.kind
            local second = first
            if second == "a" then
                local chainedAliasResult = value
            end
        end

        local function upvalueReassignment(value: Variant, replacement: Variant)
            local kind = value.kind
            local function replace()
                value = replacement
                if kind == "a" then
                    local afterUpvalueSourceReassignment = value
                end
            end
        end

        local function laterOperandCall(value: Variant, mutate: (Variant) -> ("a" | "b"))
            local kind = value.kind
            if kind == mutate(value) then
                local afterLaterOperandCall = value
            end
        end

        local function initializerCall(value: Variant, mutate: (Variant) -> boolean)
            local kind, _ = value.kind, mutate(value)
            if kind == "a" then
                local afterInitializerCall = value
            end
        end

        local function capturedWriter(value: Variant, replacement: Variant)
            local kind = value.kind
            local function mutate()
                value = replacement
            end
            if kind == "a" then
                mutate()
                local afterCapturedWriter = value
            end
        end

        local function loopBackedge(value: Variant, replacement: Variant, condition: boolean)
            local kind = value.kind
            while condition do
                if kind == "a" then
                    local afterLoopBackedge = value
                end
                value = replacement
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    CHECK_EQ("A", toString(requireTypeAtPosition({9, 43})));
    CHECK_EQ("A | B", toString(requireTypeAtPosition({18, 59})));
    CHECK_EQ("A | B", toString(requireTypeAtPosition({26, 46})));
    CHECK_EQ("A | B", toString(requireTypeAtPosition({33, 45})));
    CHECK_EQ("A | B", toString(requireTypeAtPosition({44, 44})));
    CHECK_EQ("A | B", toString(requireTypeAtPosition({52, 46})));
}

TEST_CASE_FIXTURE(Fixture, "prove_that_dataflow_analysis_isnt_doing_alias_tracking_yet")
{
    CheckResult result = check(R"(
        local function f(tag: "cat" | "dog")
            local tag2 = tag

            if tag2 == "cat" then
                local foo = tag
            else
                local foo = tag
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ(R"("cat" | "dog")", toString(requireTypeAtPosition({5, 28})));
    CHECK_EQ(R"("cat" | "dog")", toString(requireTypeAtPosition({7, 28})));
}

TEST_CASE_FIXTURE(Fixture, "fail_to_refine_a_property_of_subscript_expression")
{
    CheckResult result = check(R"(
        type Foo = { foo: number? }
        local function f(t: {Foo})
            if t[1].foo then
                local foo = t[1].foo
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    CHECK_EQ("number?", toString(requireTypeAtPosition({4, 34})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "type_annotations_arent_relevant_when_doing_dataflow_analysis")
{
    CheckResult result = check(R"(
        local function s() return "hello" end

        local function f(t: {string})
            local s1: string = t[5]
            local s2: string = s()

            if typeof(s1) == "nil" and typeof(s2) == "nil" then
                local foo = s1
                local bar = s2
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    // Function calls are treated as (potentially) `nil`, the same as table
    // access, for UX.
    CHECK_EQ("nil", toString(requireTypeAtPosition({8, 28})));
    CHECK_EQ("nil", toString(requireTypeAtPosition({9, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "function_call_with_colon_after_refining_not_to_be_nil")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        --!strict
        export type Observer<T> = {
            read complete: ((self: Observer<T>) -> ())?,
        }

        local function _f(handler: Observer<any>)
            assert(handler.complete ~= nil)
            handler:complete() -- incorrectly gives Value of type '((Observer<any>) -> ())?' could be nil
            handler.complete(handler) -- works fine, both forms should avoid the error
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(Fixture, "refinements_should_not_affect_assignment")
{
    CheckResult result = check(R"(
        local a: unknown = true
        if a == true then
            a = 'not even remotely similar to a boolean'
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refinements_should_preserve_error_suppression")
{
    CheckResult result = check(R"(
        local a: any = {}
        local b
        if typeof(a) == "table" then
           b = a.field
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(BuiltinsFixture, "many_refinements_on_val")
{
    CheckResult result = check(R"(
        local function is_nan(val: any): boolean
            return type(val) == "number" and val ~= val
        end

        local function is_js_boolean(val: any): boolean
            return not not val and val ~= 0 and val ~= "" and not is_nan(val)
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("(any) -> boolean", toString(requireType("is_nan")));
    CHECK_EQ("(any) -> boolean", toString(requireType("is_js_boolean")));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refine_unknown_to_table")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};
    // this test is DCR-only as an instance of DCR fixing a bug in the old solver

    CheckResult result = check(R"(
        local function f(a: unknown)
            if typeof(a) == "table" then
                for i, v in a do
                    return i, v
                end
            end

            error("")
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("(unknown) -> (~nil, unknown)", toString(requireType("f")));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "conditional_refinement_should_stay_error_suppressing")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        local function test(element: any?)
            if element then
                local owner = element._owner
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(BuiltinsFixture, "globals_can_be_narrowed_too")
{
    CheckResult result = check(R"(
        if typeof(string) == 'string' then
            local foo = string
        end
    )");

    if (!FFlag::DebugLuauForceOldSolver)
    {
        // CLI-114134
        CHECK("string & typeof(string)" == toString(requireTypeAtPosition(Position{2, 24})));
    }
    else
        CHECK("never" == toString(requireTypeAtPosition(Position{2, 24})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "luau_polyfill_isindexkey_refine_conjunction")
{
    ScopedFastFlag sffs[] = {
        {FFlag::DebugLuauForceOldSolver, false},
    };

    CheckResult result = check(R"(
        local function isIndexKey(k, contiguousLength)
            return type(k) == "number"
                and k <= contiguousLength -- nothing out of bounds
                and 1 <= k -- nothing illegal for array indices
                and math.floor(k) == k -- no float keys
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(BuiltinsFixture, "check_refinement_to_primitive_and_compare")
{
    ScopedFastFlag sffs[] = {
        {FFlag::DebugLuauForceOldSolver, false},
    };

    CheckResult result = check(R"(
        local function comesAfterLuau(word)
            return type(word) == "string" and word > "luau"
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    CHECK_EQ("(unknown) -> boolean", toString(requireType("comesAfterLuau")));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "luau_polyfill_isindexkey_refine_conjunction_variant")
{
    // FIXME CLI-141364: An underlying bug in normalization means the type of
    // `isIndexKey` is platform dependent.
    CheckResult result = check(R"(
        local function isIndexKey(k, contiguousLength: number)
            return type(k) == "number"
                and k <= contiguousLength -- nothing out of bounds
                and 1 <= k -- nothing illegal for array indices
                and math.floor(k) == k -- no float keys
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(BuiltinsFixture, "ex")
{
    CheckResult result = check(R"(
local function f(x: string | number)
    if typeof((x)) == "string" then
        local y = x
    end
end
)");
    TypeId t = requireTypeAtPosition({3, 18});
    CHECK("string" == toString(t));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "mutate_prop_of_some_refined_symbol")
{
    CheckResult result = check(R"(
        local function instances(): {Instance} error("") end
        local function vec3(x, y, z): Vector3 error("") end

        for _, object in ipairs(instances()) do
            if object:IsA("Part") then
                object.Position = vec3(1, 2, 3)
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "mutate_prop_of_some_refined_symbol_2")
{
    CheckResult result = check(R"(
        type Result<T, E> = never
            | { tag: "ok", value: T }
            | { tag: "err", error: E }

        local function results(): {Result<number, string>} error("") end

        for _, res in ipairs(results()) do
            if res.tag == "ok" then
                res.value = 7
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(BuiltinsFixture, "ensure_t_after_return_references_all_reachable_points")
{
    CheckResult result = check(R"(
        local t = {}

        local function f(k: string)
            if t[k] ~= nil then
                return
            end

            t[k] = 5
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    if (!FFlag::DebugLuauForceOldSolver)
        CHECK_EQ("{ [string]: number }", toString(requireTypeAtPosition({8, 12}), {true}));
    else
        CHECK_EQ("{| [string]: number |}", toString(requireTypeAtPosition({8, 12}), {true}));
}

TEST_CASE_FIXTURE(Fixture, "long_disjunction_of_refinements_should_not_trip_recursion_counter")
{
    CHECK_NOTHROW(check(R"(
function(obj)
    if script.Parent.SeatNumber.Value == "1D" or
    script.Parent.SeatNumber.Value == "2D" or
    script.Parent.SeatNumber.Value == "3D" or
    script.Parent.SeatNumber.Value == "4D" or
    script.Parent.SeatNumber.Value == "5D" or
    script.Parent.SeatNumber.Value == "6D" or
    script.Parent.SeatNumber.Value == "7D" or
    script.Parent.SeatNumber.Value == "8D" or
    script.Parent.SeatNumber.Value == "9D" or
    script.Parent.SeatNumber.Value == "10D" or
    script.Parent.SeatNumber.Value == "11D" or
    script.Parent.SeatNumber.Value == "12D" or
    script.Parent.SeatNumber.Value == "13D" or
    script.Parent.SeatNumber.Value == "14D" or
    script.Parent.SeatNumber.Value == "15D" or
    script.Parent.SeatNumber.Value == "16D" or
    script.Parent.SeatNumber.Value == "1C" or
    script.Parent.SeatNumber.Value == "2C" or
    script.Parent.SeatNumber.Value == "3C" or
    script.Parent.SeatNumber.Value == "4C" or
    script.Parent.SeatNumber.Value == "5C" or
    script.Parent.SeatNumber.Value == "6C" or
    script.Parent.SeatNumber.Value == "7C" or
    script.Parent.SeatNumber.Value == "8C" or
    script.Parent.SeatNumber.Value == "9C" or
    script.Parent.SeatNumber.Value == "10C" or
    script.Parent.SeatNumber.Value == "11C" or
    script.Parent.SeatNumber.Value == "12C" or
    script.Parent.SeatNumber.Value == "13C" or
    script.Parent.SeatNumber.Value == "14C" or
    script.Parent.SeatNumber.Value == "15C" or
    script.Parent.SeatNumber.Value == "16C" then
end
)"));
}

TEST_CASE_FIXTURE(Fixture, "more_complex_long_disjunction_of_refinements_shouldnt_trip_ice")
{
    CHECK_NOTHROW(check(R"(
script:connect(function(obj)
	if script.Parent.SeatNumber.Value == "1D" or
    script.Parent.SeatNumber.Value == "2D" or
    script.Parent.SeatNumber.Value == "3D" or
    script.Parent.SeatNumber.Value == "4D" or
    script.Parent.SeatNumber.Value == "5D" or
    script.Parent.SeatNumber.Value == "6D" or
    script.Parent.SeatNumber.Value == "7D" or
    script.Parent.SeatNumber.Value == "8D" or
    script.Parent.SeatNumber.Value == "9D" or
    script.Parent.SeatNumber.Value == "10D" or
    script.Parent.SeatNumber.Value == "11D" or
    script.Parent.SeatNumber.Value == "12D" or
    script.Parent.SeatNumber.Value == "13D" or
    script.Parent.SeatNumber.Value == "14D" or
    script.Parent.SeatNumber.Value == "15D" or
    script.Parent.SeatNumber.Value == "16D" or
    script.Parent.SeatNumber.Value == "1C" or
    script.Parent.SeatNumber.Value == "2C" or
    script.Parent.SeatNumber.Value == "3C" or
    script.Parent.SeatNumber.Value == "4C" or
    script.Parent.SeatNumber.Value == "5C" or
    script.Parent.SeatNumber.Value == "6C" or
    script.Parent.SeatNumber.Value == "7C" or
    script.Parent.SeatNumber.Value == "8C" or
    script.Parent.SeatNumber.Value == "9C" or
    script.Parent.SeatNumber.Value == "10C" or
    script.Parent.SeatNumber.Value == "11C" or
    script.Parent.SeatNumber.Value == "12C" or
    script.Parent.SeatNumber.Value == "13C" or
    script.Parent.SeatNumber.Value == "14C" or
    script.Parent.SeatNumber.Value == "15C" or
    script.Parent.SeatNumber.Value == "16C" then
    end)
)"));
}

TEST_CASE_FIXTURE(Fixture, "refinements_should_avoid_building_up_big_intersect_families")
{
    CHECK_NOTHROW(check(R"(
script:connect(function(obj)
	if script.Parent.SeatNumber.Value == "1D" or script.Parent.SeatNumber.Value == "2D" or script.Parent.SeatNumber.Value == "3D" or script.Parent.SeatNumber.Value == "4D" or script.Parent.SeatNumber.Value == "5D" or script.Parent.SeatNumber.Value == "6D" or script.Parent.SeatNumber.Value == "7D" or script.Parent.SeatNumber.Value == "8D" or script.Parent.SeatNumber.Value == "9D" or script.Parent.SeatNumber.Value == "10D" or script.Parent.SeatNumber.Value == "11D" or script.Parent.SeatNumber.Value == "12D" or script.Parent.SeatNumber.Value == "13D" or script.Parent.SeatNumber.Value == "14D" or script.Parent.SeatNumber.Value == "15D" or script.Parent.SeatNumber.Value == "16D" or script.Parent.SeatNumber.Value == "1C" or script.Parent.SeatNumber.Value == "2C" or script.Parent.SeatNumber.Value == "3C" or script.Parent.SeatNumber.Value == "4C" or script.Parent.SeatNumber.Value == "5C" or script.Parent.SeatNumber.Value == "6C" or script.Parent.SeatNumber.Value == "7C" or script.Parent.SeatNumber.Value == "8C" or script.Parent.SeatNumber.Value == "9C" or script.Parent.SeatNumber.Value == "10C" or script.Parent.SeatNumber.Value == "11C" or script.Parent.SeatNumber.Value == "12C" or script.Parent.SeatNumber.Value == "13C" or script.Parent.SeatNumber.Value == "14C" or script.Parent.SeatNumber.Value == "15C" or script.Parent.SeatNumber.Value == "16C" then
		if p.Name == script.Parent.Parent.Parent.Parent.Parent.Parent.MainParts.CD.SurfaceGui[script.Parent.SeatNumber.Value].Player.Value or script.Parent.Parent.Parent.Parent.Parent.Parent.MainParts.CD.SurfaceGui[script.Parent.SeatNumber.Value].Player.Value == "" then
		else
			if script.Parent:FindFirstChild("SeatWeld") then
			end
		end
	else
		if p.Name == script.Parent.Parent.Parent.Parent.Parent.Parent.MainParts.AB.SurfaceGui[script.Parent.SeatNumber.Value].Player.Value or script.Parent.Parent.Parent.Parent.Parent.Parent.MainParts.AB.SurfaceGui[script.Parent.SeatNumber.Value].Player.Value == "" then
			print("Allowed")
		else
			if script.Parent:FindFirstChild("SeatWeld") then
			end
		end
	end
end)
)"));
}

TEST_CASE_FIXTURE(Fixture, "refinements_table_intersection_limits" * doctest::timeout(1.5))
{
    CheckResult result = check(R"(
--!strict
type Dir = {
    a: number?, b: number?, c: number?, d: number?, e: number?, f: number?,
    g: number?, h: number?, i: number?, j: number?, k: number?, l: number?,
    m: number?, n: number?, o: number?, p: number?, q: number?, r: number?,
}

local function test(dirs: {Dir})
    for k, dir in dirs
        local success, message = pcall(function()
            assert(dir.a == nil or type(dir.a) == "number")
            assert(dir.b == nil or type(dir.b) == "number")
            assert(dir.c == nil or type(dir.c) == "number")
            assert(dir.d == nil or type(dir.d) == "number")
            assert(dir.e == nil or type(dir.e) == "number")
            assert(dir.f == nil or type(dir.f) == "number")
            assert(dir.g == nil or type(dir.g) == "number")
            assert(dir.h == nil or type(dir.h) == "number")
            assert(dir.i == nil or type(dir.i) == "number")
            assert(dir.j == nil or type(dir.j) == "number")
            assert(dir.k == nil or type(dir.k) == "number")
            assert(dir.l == nil or type(dir.l) == "number")
            assert(dir.m == nil or type(dir.m) == "number")
            assert(dir.n == nil or type(dir.n) == "number")
            assert(dir.o == nil or type(dir.o) == "number")
            assert(dir.p == nil or type(dir.p) == "number")
            assert(dir.q == nil or type(dir.q) == "number")
            assert(dir.r == nil or type(dir.r) == "number")
            assert(dir.t == nil or type(dir.t) == "number")
            assert(dir.u == nil or type(dir.u) == "number")
            assert(dir.v == nil or type(dir.v) == "number")
            local checkpoint = dir

            checkpoint.w = 1
        end)
        assert(success)
    end
end
    )");
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "typeof_instance_refinement")
{
    CheckResult result = check(R"(
        local function f(x: Instance | Vector3)
            if typeof(x) == "Instance" then
                local foo = x
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("Instance", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("Vector3", toString(requireTypeAtPosition({5, 28})));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "typeof_instance_error")
{
    CheckResult result = check(R"(
        local function f(x: Part)
            if typeof(x) == "Instance" then
                local foo : Folder = x
            end
        end
    )");

    LUAU_REQUIRE_ERROR_COUNT(1, result);
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "typeof_instance_isa_refinement")
{
    CheckResult result = check(R"(
        local function f(x: Part | Folder | string)
            if typeof(x) == "Instance" then
                local foo = x
                if foo:IsA("Folder") then
                    local bar = foo
                end
            else
                local foo = x
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);

    CHECK_EQ("Folder | Part", toString(requireTypeAtPosition({3, 28})));
    CHECK_EQ("Folder", toString(requireTypeAtPosition({5, 32})));
    CHECK_EQ("string", toString(requireTypeAtPosition({8, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "nonnil_refinement_on_generic")
{
    CheckResult result = check(R"(
        local function printOptional<T>(item: T?, printer: (T) -> string): string
            if item ~= nil then
                return printer(item)
            else
                return ""
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    if (!FFlag::DebugLuauForceOldSolver)
        CHECK_EQ("T & ~nil", toString(requireTypeAtPosition({3, 31})));
    else
        CHECK_EQ("T", toString(requireTypeAtPosition({3, 31})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "truthy_refinement_on_generic")
{
    CheckResult result = check(R"(
        local function printOptional<T>(item: T?, printer: (T) -> string): string
            if item then
                return printer(item)
            else
                return ""
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    if (!FFlag::DebugLuauForceOldSolver)
        CHECK_EQ("T & ~(false?)", toString(requireTypeAtPosition({3, 31})));
    else
        CHECK_EQ("T", toString(requireTypeAtPosition({3, 31})));
}

TEST_CASE_FIXTURE(Fixture, "truthy_call_of_function_with_table_value_as_argument_should_not_refine_value_as_never")
{
    CheckResult result = check(R"(
        type Item = {}

        local function predicate(value: Item): boolean
            return true
        end

        local function checkValue(value: Item)
            if predicate(value) then
                local _ = value
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    CHECK_EQ("Item", toString(requireTypeAtPosition({8, 27})));
    CHECK_EQ("Item", toString(requireTypeAtPosition({9, 28})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "function_calls_are_not_nillable")
{
    LUAU_CHECK_NO_ERRORS(check(R"(
        local BEFORE_SLASH_PATTERN = "^(.*)[\\/]"
        function operateOnPath(path: string): string?
            local fileName = string.gsub(path, BEFORE_SLASH_PATTERN, "")
            if string.match(fileName, "^init%.") then
                return "path=" .. fileName
            end
            return nil
        end
    )"));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "oss_1528_method_calls_are_not_nillable")
{
    LUAU_CHECK_NO_ERRORS(check(R"(
        type RunService = {
            IsRunning: (RunService) -> boolean
        }
        type Game = {
            GetRunService: (Game) -> RunService
        }
        local function getServices(g: Game): RunService
            local service = g:GetRunService()
            if service:IsRunning() then
                return service
            end
            error("Oh no! The service isn't running!")
        end
    )"));
}

TEST_CASE_FIXTURE(Fixture, "oss_1687_equality_shouldnt_leak_nil")
{
    LUAU_REQUIRE_NO_ERRORS(check(R"(
        --!strict
        function returns_two(): number
            return 2
        end

        function is_two(num: number): boolean
            return num==2
        end

        local my_number = returns_two()

        if my_number == 2 then
            is_two(my_number) --type error, my_number: number?
        end
    )"));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "oss_1451")
{
    ScopedFastFlag _{FFlag::DebugLuauForceOldSolver, false};

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        type Part = {
            HasTag: (Part, string) -> boolean,
            Name: string,
        }
        local myList = {} :: {Part}
        local nextPart = (table.remove(myList)) :: Part

        if nextPart:HasTag("foo") then
          return
        end

        print(nextPart.Name)

    )"));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "cannot_call_a_function_single")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        local function invokeDisconnect(d: unknown)
            if type(d) == "function" then
                d()
            end
        end
    )");

    LUAU_REQUIRE_ERROR_COUNT(1, result);
    CHECK_EQ("The type function is not precise enough for us to determine the appropriate result type of this call.", toString(result.errors[0]));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "cli_140033_refine_union_of_extern_types")
{
    LUAU_REQUIRE_NO_ERRORS(check(R"(
        --!strict
        local function getImageLabel(vars: { Instance }): Folder | Part | nil
            for _, item in vars do
                if item:IsA("Folder") or item:IsA("Part") then
                    return item
                end
            end
            return nil
        end
    )"));

    CHECK_EQ("Folder | Part", toString(requireTypeAtPosition({5, 28})));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "discriminate_union_of_extern_types_by_readonly_identity_property")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        local function exact(value: FirstVariant | SecondVariant)
            if value.Kind == firstKindValue then
                local selected = value
            else
                local rejected = value
            end
        end

        local function commonKind(value: FirstVariant | SecondVariant, kind: Discriminant)
            if value.Kind == kind then
                local selected = value
            else
                local rejected = value
            end
        end

        local function common(value: FirstVariant | CommonVariant)
            if value.Kind == firstKindValue then
                local selected = value
            end
        end

        local function broad(value: BroadVariant | SecondVariant)
            if value.Kind == firstKindValue then
                local selected = value
            else
                local rejected = value
            end
        end

        local function writable(value: WritableVariant | SecondVariant)
            if value.Kind == firstKindValue then
                local selected = value
            end
        end

        local function unknown(value: UnknownVariant | SecondVariant)
            if value.Kind == firstKindValue then
                local selected = value
            end
        end


        local function ambiguous(value: AmbiguousVariant | SecondVariant)
            if value.Kind == firstKindValue then
                local selected = value
            else
                local rejected = value
            end
        end

    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    CHECK_EQ("FirstVariant", toString(requireTypeAtPosition({3, 33})));
    CHECK_EQ("FirstVariant | SecondVariant", toString(requireTypeAtPosition({5, 33})));
    CHECK_EQ("FirstVariant | SecondVariant", toString(requireTypeAtPosition({11, 33})));
    CHECK_EQ("FirstVariant | SecondVariant", toString(requireTypeAtPosition({13, 33})));
    CHECK_EQ("CommonVariant | FirstVariant", toString(requireTypeAtPosition({19, 33})));
    CHECK_EQ("BroadVariant & { read Kind: FirstKind }", toString(requireTypeAtPosition({25, 33})));
    CHECK_EQ("BroadVariant | SecondVariant", toString(requireTypeAtPosition({27, 33})));
    CHECK_EQ("WritableVariant", toString(requireTypeAtPosition({33, 33})));
    CHECK_EQ("UnknownVariant & { read Kind: FirstKind }", toString(requireTypeAtPosition({39, 33})));
    CHECK_EQ("AmbiguousVariant & { read Kind: FirstKind }", toString(requireTypeAtPosition({46, 33})));
    CHECK_EQ("AmbiguousVariant | SecondVariant", toString(requireTypeAtPosition({48, 33})));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "impossible_extern_discriminant_comparisons_remain_conservative")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        local function recursive(value: RecursiveVariant | SecondVariant)
            if value.Kind == firstKindValue then
                local selected = value
            else
                local rejected = value
            end
        end

        local function unrelated(value: FirstVariant | SecondVariant)
            if value.Kind == unrelatedKindValue then
                local selected = value
            else
                local rejected = value
            end
        end
    )");

    LUAU_REQUIRE_ERROR_COUNT(2, result);
    const auto* recursiveComparison = get<CannotCompareUnrelatedTypes>(result.errors[0]);
    const auto* unrelatedComparison = get<CannotCompareUnrelatedTypes>(result.errors[1]);
    REQUIRE(recursiveComparison);
    REQUIRE(unrelatedComparison);
    CHECK_EQ(AstExprBinary::CompareEq, recursiveComparison->op);
    CHECK_EQ(AstExprBinary::CompareEq, unrelatedComparison->op);
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "missing_extern_discriminant_property_is_conservative")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        local function missing(value: FirstVariant | MissingVariant)
            if value.Kind == firstKindValue then
                local selected = value
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
    CHECK_EQ("FirstVariant | MissingVariant", toString(requireTypeAtPosition({3, 33})));
}

TEST_CASE_FIXTURE(RefinementExternTypeFixture, "cannot_call_a_function_union")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        type Disconnectable = {
            Disconnect: (self: Disconnectable) -> (...any);
        } | {
            disconnect: (self: Disconnectable) -> (...any)
        } | ExternScriptConnection

        local x: Disconnectable = workspace.ChildAdded:Connect(function()
            print("child added")
        end)

        if type(x.Disconnect) == "function" then
            x:Disconnect()
        end
    )");

    LUAU_REQUIRE_ERROR_COUNT(2, result);

    // FIXME CLI-157125: It's a bit clowny that we return a union of
    // functions containing `function` here, but it looks like a side
    // effect of how we execute `hasProp`.
    std::string expectedError = "Cannot call a value of type function in union:\n"
                                "  ((ExternScriptConnection) -> ()) | function | t2 where t1 = ExternScriptConnection | { Disconnect: t2 } | { "
                                "disconnect: (t1) -> (...any) } ; t2 = (t1) -> (...any)";

    CHECK_EQ(toString(result.errors[1]), expectedError);
}

TEST_CASE_FIXTURE(BuiltinsFixture, "oss_1835")
{
    LUAU_REQUIRE_NO_ERRORS(check(R"(
        --!strict
        local t: {name: string}? = nil

        function f()
            local name = if t then t.name else "name"
        end
    )"));

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        --!strict
        local t: {name: string}? = nil

        function f()
            if t then end
            local name = if t then t.name else "name"
        end
    )"));

    CheckResult result = check(R"(
        local t: {name: string}? = nil
        if t then end
        print(t.name)
        local name = if t then t.name else "name"
    )");
    LUAU_REQUIRE_ERROR_COUNT(1, result);
    CHECK(get<OptionalValueAccess>(result.errors[0]));
}

TEST_CASE_FIXTURE(Fixture, "limit_complexity_of_arithmetic_type_functions" * doctest::timeout(0.5))
{
    ScopedFastFlag _{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        local Hermite = {}

        function Hermite:__init(p0, p1, m0, m1)
            self[1] = {
                p0.x;
                p0.y;
                p0.z;
            }
            self[2] = {
                m0.x;
                m0.y;
                m0.z;
            }
            self[3] = {
                3*(p1.x - p0.x) - 2*m0.x - m1.x;
                3*(p1.y - p0.y) - 2*m0.y - m1.y;
                3*(p1.z - p0.z) - 2*m0.z - m1.z;
            }
        end

        return Hermite
    )");

    // We do not care what the errors are, only that this type checks in a
    // reasonable amount of time.
    LUAU_REQUIRE_ERRORS(result);
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refine_by_no_refine_should_always_reduce")
{
    // NOTE: Previously this only required two flags, but clipping a flag around
    // how we report constraint solving incomplete errors revealed that this
    // test would always fail to solve all constraints, except under eager
    // generalization.
    ScopedFastFlag _{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        function foo(t): boolean return true end

        function select<K, V>(t: { [K]: V }, columns: { K }): { [K]: V }
            local result = {}
            if foo(t) then
                for k, v in t do
                    if table.find(columns, k) then
                        result[k] = v -- was TypeError: Type function instance refine<intersect<K, ~nil>, *no-refine*> is uninhabited
                    end
                end
            else
                for k, v in pairs(t) do
                    if table.find(columns, k) then
                        result[k] = v
                    end
                end
            end
            return result
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(result);
}

TEST_CASE_FIXTURE(Fixture, "table_name_index_without_prior_assignment_from_branch")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    // The important part of this test case is:
    // - `CharEntry` is represented as a phi node in the data flow graph;
    // - We never _set_ `CharEntry.Player` prior to accessing it.
    CheckResult results = check(R"(
        local GetDictionary : (unknown, boolean) -> { Player: {} }? = nil :: any

        local CharEntry = GetDictionary(nil, false)
        if not CharEntry then
            CharEntry = GetDictionary(nil, true)
        end

        local x = CharEntry.Player
    )");

    LUAU_REQUIRE_ERROR_COUNT(1, results);
    CHECK(get<OptionalValueAccess>(results.errors[0]));
    CHECK_EQ("{  }", toString(requireType("x")));
}

TEST_CASE_FIXTURE(Fixture, "optional_local_assignment_preserves_the_other_branch_refinement_at_a_join")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        type Value = { [string]: true? }

        local value: Value? = nil
        if value == nil then
            value = {}
        end

        value.enabled = true
    )"));

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        type Value = { [string]: true? }
        type Output = { [string]: Value? }

        local output: Output = {}
        local value: Value? = nil
        if value == nil then
            value = {}
        end

        output.entry = value
        value.enabled = true
    )"));

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        type Value = { [string]: true? }

        local value: Value? = nil
        local function read()
            return value
        end

        if value == nil then
            value = {}
        end

        read()
        value.enabled = true
    )"));

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        type Value = { [string]: true? }

        local value: Value? = nil
        if value == nil then
            value = nil
            value = {}
        end

        value.enabled = true
    )"));
}

TEST_CASE_FIXTURE(Fixture, "optional_local_join_does_not_hide_later_optional_paths")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult reassigned = check(R"(
        type Value = { [string]: true? }

        local value: Value? = nil
        if value == nil then
            value = {}
        end

        value = nil
        value.enabled = true
    )");
    LUAU_REQUIRE_ERROR_COUNT(1, reassigned);
    CHECK(get<NotATable>(reassigned.errors[0]));

    CheckResult optionalBranch = check(R"(
        type Value = { [string]: true? }

        local function write(flag: boolean)
            local value: Value? = nil
            if flag then
                value = {}
            end

            value.enabled = true
        end
    )");
    LUAU_REQUIRE_ERROR_COUNT(1, optionalBranch);
    CHECK(get<OptionalValueAccess>(optionalBranch.errors[0]));

    CheckResult partialAssignment = check(R"(
        type Value = { [string]: true? }

        local function write(flag: boolean)
            local value: Value? = nil
            if value == nil then
                if flag then
                    value = {}
                end
            end

            value.enabled = true
        end
    )");
    LUAU_REQUIRE_ERROR_COUNT(1, partialAssignment);
    CHECK(get<OptionalValueAccess>(partialAssignment.errors[0]));

    CheckResult finalAssignmentIsOptional = check(R"(
        type Value = { [string]: true? }

        local value: Value? = nil
        if value == nil then
            value = {}
            value = nil
        end

        value.enabled = true
    )");
    LUAU_REQUIRE_ERROR_COUNT(1, finalAssignmentIsOptional);
    CHECK(get<OptionalValueAccess>(finalAssignmentIsOptional.errors[0]));

    CheckResult callMayWrite = check(R"(
        type Value = { [string]: true? }

        local value: Value? = nil
        local function clear()
            value = nil
        end

        if value == nil then
            value = {}
        end

        clear()
        value.enabled = true
    )");
    LUAU_REQUIRE_ERROR_COUNT(1, callMayWrite);
    CHECK(get<OptionalValueAccess>(callMayWrite.errors[0]));
}

TEST_CASE_FIXTURE(Fixture, "cli_120460_table_access_on_phi_node")
{
    LUAU_REQUIRE_NO_ERRORS(check(R"(
        --!strict
        local function foo(bar: string): string
            local baz: boolean = true
            if baz then
                local _ = (bar:sub(1))
            else
                local _ = (bar:sub(1))
            end
            return bar:sub(2) -- previously this would be `...never`
        end
    )"));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refinements_from_and_should_not_refine_to_never")
{
    ScopedFastFlag sffs[] = {
        {FFlag::DebugLuauForceOldSolver, false},
    };

    loadDefinition(R"(
        declare extern type Config with
            KeyboardEnabled: boolean
            MouseEnabled: boolean
        end
    )");

    CheckResult results = check(R"(
        local config: Config
        local function serialize()
            if config.KeyboardEnabled and config.MouseEnabled then
                return 0
            else
                print(config)
                return 1
            end
        end
    )");

    LUAU_REQUIRE_NO_ERRORS(results);

    CHECK_EQ("(Config & { read KeyboardEnabled: false? }) | (Config & { read MouseEnabled: false? })", toString(requireTypeAtPosition({6, 24})));
}

TEST_CASE_FIXTURE(Fixture, "force_simplify_constraint_doesnt_drop_blocked_type")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult results = check(R"(
        local function track(instance): boolean
            local isBasePart = instance:IsA("BasePart")
            local isCharacter = false
            if not isBasePart then
                isCharacter = instance:FindFirstChildOfClass("Humanoid") and instance:FindFirstChild("HumanoidRootPart")
            end
            return isCharacter
        end
    )");

    // NOTE: This should have *no* errors but due to a constraint cycle
    // between the `and` type function and the subtype constraint of the
    // return type, we end up sometimes being unable to reduce this properly.

    LUAU_REQUIRE_ERROR_COUNT(1, results);
    CHECK(get<TypeMismatch>(results.errors[0]));
}

TEST_CASE_FIXTURE(Fixture, "len_operator_in_if_is_just_a_proposition")
{
    ScopedFastFlag _[] = {
        {FFlag::DebugLuauForceOldSolver, false},
    };

    CheckResult result = check(R"(
type Pool = { x : number }
local pool = p :: Pool
if #pool then
    local y = pool
end
)");
    TypeId ty = requireTypeAtPosition({4, 14});
    CHECK(toString(ty) != "never");
}

TEST_CASE_FIXTURE(Fixture, "unm_operator_is_just_a_proposition")
{
    ScopedFastFlag _[] = {
        {FFlag::DebugLuauForceOldSolver, false},
    };

    CheckResult result = check(R"(
type Pool = { x : number }
local pool = p :: Pool
if -pool then
    local y = pool
end
)");
    TypeId ty = requireTypeAtPosition({4, 14});
    CHECK(toString(ty) != "never");
}

TEST_CASE_FIXTURE(BuiltinsFixture, "inline_if_conditional_context")
{
    LUAU_REQUIRE_NO_ERRORS(check(R"(
        --!strict

        type Value<T> = {
            kind: "value",
            value: T
        }

        local function peek<T>(state: Value<T> | T): T
            return if typeof(state) == "table" and state.kind == "value"
                then (state :: Value<T>).value :: T
                else state :: T
        end
    )"));
}

TEST_CASE_FIXTURE(Fixture, "oss_1517_equality_doesnt_add_nil")
{
    LUAU_REQUIRE_NO_ERRORS(check(R"(
        type MyType = {
            data: any
        }

        local function createMyType(): MyType
            local obj = { data = {} }
            return obj
        end

        local function testTypeInference()
            local a: MyType = createMyType()
            local b: MyType = createMyType()

            if a == b then
                local c: MyType = b
                local value = b.data
            end
        end
    )"));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "typeof_refinement_context")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        --!strict

        local x = {} :: unknown

        if typeof(x) == "table" then
            if typeof(x.transform) == "function" then
            	local y = x.transform
            end
        end
    )"));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "assert_and_typeof_refinement_context")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        --!strict

        local x = {} :: unknown

        if typeof(x) == "table" then
            assert(typeof(x.transform) == "function")
        end
    )"));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "foo_call_should_not_refine")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        --!strict

        local x = {} :: unknown
        local function foo(_: boolean) end

        if typeof(x) == "table" then
            foo(typeof(x.transform) == "function")
        end
    )");

    LUAU_REQUIRE_ERROR_COUNT(1, result);
    CHECK_EQ("Type 'table' does not have key 'transform'", toString(result.errors[0]));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "assert_call_should_not_refine_despite_typeof")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        --!strict
        local function foo(_: any)
            return true
        end

        local function f(x: unknown)
            if typeof(x) == "table" then
                assert(foo(typeof(x.bar)))
            end
        end
    )");

    LUAU_REQUIRE_ERROR_COUNT(1, result);
    CHECK_EQ("Type 'table' does not have key 'bar'", toString(result.errors[0]));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "non_conditional_context_in_if_should_not_refine")
{
    ScopedFastFlag sff{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        local function bing(_: any) end
        local function foobar(x: unknown)
            assert(typeof(x) == "table")
            if bing(x.foo) then
            end
        end
    )");

    LUAU_REQUIRE_ERROR_COUNT(1, result);
    CHECK_EQ("Type 'table' does not have key 'foo'", toString(result.errors[0]));
}

TEST_CASE_FIXTURE(Fixture, "type_function_reduction_with_union_type_application" * doctest::timeout(0.5))
{
    ScopedFastFlag sffs[] = {
        {FFlag::DebugLuauForceOldSolver, false},
        {FFlag::DebugLuauAssertOnForcedConstraint, true},
    };

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        local lastTick = 0
        local jumpAnimTime = 0
        local toolAnimTime = 0

        function move(time, tool, animStringValueObject)
            local deltaTime = time - lastTick
            lastTick = time

            if jumpAnimTime > 0 then
                jumpAnimTime = jumpAnimTime - deltaTime
            end

            if animStringValueObject then
                toolAnimTime = time + .3
            end

            if time > toolAnimTime then
            end
        end
    )"));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "refine_any_and_unknown_should_still_be_any")
{
    LUAU_REQUIRE_NO_ERRORS(check(R"(
        local REACT_FRAGMENT_TYPE = (nil :: any)
        local function typeOf(object: any)
            local __type = object.type

            if __type == REACT_FRAGMENT_TYPE then
                return __type
            else
                return __type
                    and typeof(__type) == "table"
                    and __type["$$typeof"]
            end
        end
    )"));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "cli_181100_fast_track_refinement_against_unknown")
{
    ScopedFastFlag sffs[] = {
        {FFlag::DebugLuauForceOldSolver, false},
        {FFlag::DebugLuauAssertOnForcedConstraint, true},
    };

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        --!strict

        local Class = {}
        Class.__index = Class

        type Class = setmetatable<{ A: number }, typeof(Class)>

        function Class.Foo(x: Class, y: Class, z: Class)
            if y == z then
                return
            end
            local bar = y.A
            print(bar)
        end
    )"));

    CHECK_EQ("number", toString(requireTypeAtPosition({13, 19})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "cli_181549_refined_string_should_be_subtype_of_string")
{
    ScopedFastFlag _{FFlag::DebugLuauForceOldSolver, false};

    LUAU_REQUIRE_NO_ERRORS(check(Mode::Nonstrict, R"(
      local hello : string = "world"

      if hello == "" then
          return
      end

      string.find(hello, "bye")
    )"));
}

TEST_CASE_FIXTURE(Fixture, "cli_184413_refinement_of_union_of_read_types_is_read_type")
{
    LUAU_REQUIRE_NO_ERRORS(check(R"(
        export type States = "Closed" | "Closing" | "Opening" | "Open"
        export type MyType<A = any> = {
            State: States,
            IsOpen: boolean,
            Open: (self: MyType<A>) -> (),
        }

        local value = {} :: MyType

        function value:Open()
            if self.IsOpen == true then
            elseif self.State == "Closing" or self.State == "Opening" then
                -- Prior, this line errored as we were erroneously refining
                -- `self` with `{ State: "Closing" | "Opening" }` rather
                -- than `{ read State: "Closing" | "Opening" }
                self:Open()
            end
        end
    )"));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "type_vector_refine")
{
    ScopedFastFlag _[] = {{FFlag::DebugLuauForceOldSolver, false}};

    CheckResult result = check(R"(
        function foo(x: unknown)
            if type(x) == "vector" then
                local y = x.y
                local z = y.bad
            end
        end
    )");

    LUAU_REQUIRE_ERROR_COUNT(1, result);
    REQUIRE(get<UnknownProperty>(result.errors[0]));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "indexing_into_error_gives_error")
{
    ScopedFastFlag _{FFlag::LuauIndexingIntoErrorGivesError, true};

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        local function keyExtractor(item: any, index: number): string
            if typeof(item) == "table" and item.key ~= nil then
                return item.key
            end
            if typeof(item) == "table" and item.id ~= nil then
                return item.id
            end
            return tostring(index)
        end
    )"));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "property_refinements_preserve_recursive_metatable_receiver")
{
    ScopedFastFlag _{FFlag::DebugLuauForceOldSolver, false};

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        --!strict

        type TickPlan = {
            action: (() -> ())?,
        }
        type CharacterState = {
            alive: boolean,
            root: {
                position: number,
            },
        }
        type FighterState = {
            environmentId: string?,
            character: {
                state: CharacterState,
            },
        }
        type Controller = {
            getPosition: (Controller) -> number,
        }
        type Context = {
            fighterState: FighterState,
            controller: Controller,
        }

        local Class = {}
        Class.__index = Class

        type Data = {
            enabled: boolean,
            context: Context?,
        }
        type Class = setmetatable<Data, typeof(Class)>

        function Class.reset(self: Class) end

        function Class.plan(self: Class, position: number, rootPosition: number): TickPlan
            return {}
        end

        function Class.apply(self: Class, plan: TickPlan, context: Context) end

        function Class.update(self: Class)
            local context = self.context
            if context == nil then
                self:reset()
                return
            end

            local fighterState = context.fighterState
            if fighterState.environmentId == nil or not self.enabled then
                self:reset()
                return
            end

            local characterState = fighterState.character.state
            if not characterState.alive then
                self:reset()
                return
            end

            local controller = context.controller
            local position = controller:getPosition()
            local plan = self:plan(position, characterState.root.position)
            self:apply(plan, context)

            local action = plan.action
            if action ~= nil then
                action()
            end
        end
    )"));

    CHECK_EQ("(() -> ())?", toString(requireTypeAtPosition({67, 34})));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "impossible_property_refinement_of_recursive_metatable_is_never")
{
    ScopedFastFlag _{FFlag::DebugLuauForceOldSolver, false};

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        --!strict

        local Class = {}
        Class.__index = Class

        type Class = setmetatable<{ tag: "a" }, typeof(Class)>

        function Class.check(self: Class)
            if self.tag == "b" then
                local impossible: never = self
            end
        end
    )"));
}

TEST_CASE_FIXTURE(BuiltinsFixture, "property_refined_metatable_preserves_writable_table_capabilities")
{
    ScopedFastFlag solverFlag{FFlag::DebugLuauForceOldSolver, false};

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        --!strict

        local Class = {}
        Class.__index = Class

        type Data<T> = {
            locked: T?,
            requested: boolean,
        }
        type Class<T> = setmetatable<Data<T>, typeof(Class)>

        local function update<T>(self: Class<T>)
            if self.locked == nil then
                self.requested = true
            else
                self.locked = nil
            end
        end
    )"));

    CheckResult invalidWrites = check(R"(
        --!strict

        local Class = {}
        Class.__index = Class

        type Data = {
            locked: number?,
            requested: boolean,
        }
        type Class = setmetatable<Data, typeof(Class)>

        local function update(self: Class)
            if self.locked == nil then
                self.requested = "yes"
            else
                self.locked = "no"
            end
        end
    )");

    LUAU_REQUIRE_ERROR_COUNT(2, invalidWrites);
    CHECK(get<TypeMismatch>(invalidWrites.errors[0]));
    CHECK(get<TypeMismatch>(invalidWrites.errors[1]));
}

TEST_CASE_FIXTURE(Fixture, "post_if_phi_preserves_the_refined_incoming_discriminated_arm")
{
    ScopedFastFlag _{FFlag::DebugLuauForceOldSolver, false};

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        type Build = { ready: false } | { ready: true, value: number }
        local build: Build = { ready = false }

        if not build.ready then
            build = { ready = true, value = 1 }
        end

        return build.value
    )"));

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        type Build = { ready: false } | { ready: true, value: number }
        local holder: { build: Build } = { build = { ready = false } }
        local build = holder.build

        if not build.ready then
            build = { ready = true, value = 1 }
            holder.build = build
        end

        return build.value
    )"));

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        type Build = { ready: false } | { ready: true, value: number }
        local build: Build = { ready = false }

        local function isReady()
            return build.ready
        end

        if not build.ready then
            build = { ready = true, value = 1 }
        end

        isReady()
        return build.value
    )"));

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        type Build = { ready: false } | { ready: true, value: number }
        local build: Build = { ready = false }

        if not build.ready then
            build = { ready = false }
            build = { ready = true, value = 1 }
        end

        return build.value
    )"));

    LUAU_REQUIRE_NO_ERRORS(check(R"(
        type Build<T> = { ready: true, value: T } | { ready: false }

        local function finish<T>(build: Build<T>, value: T): T
            if not build.ready then
                build = { ready = true, value = value }
            end

            return build.value
        end

        local function finishAfterStore<T>(build: Build<T>, value: T): T
            local holder = { build = build }

            if not build.ready then
                build = { ready = true, value = value }
            end

            holder.build = build
            return build.value
        end
    )"));
}

TEST_CASE_FIXTURE(Fixture, "post_if_phi_does_not_preserve_unproven_discriminated_arms")
{
    ScopedFastFlag _{FFlag::DebugLuauForceOldSolver, false};

    CheckResult result = check(R"(
        type Build<T> = { ready: true, value: T } | { ready: false }
        type ReadyBuild<T> = { ready: true, value: T }

        local function withoutReassignment<T>(build: Build<T>): T
            if not build.ready then
            end

            return build.value
        end

        local function afterUnionWrite<T>(build: Build<T>, ready: ReadyBuild<T>, other: Build<T>): T
            if not build.ready then
                build = ready
            end

            build = other
            return build.value
        end

        local function withoutReassignmentOnEveryPath<T>(build: Build<T>, ready: ReadyBuild<T>, condition: boolean): T
            if not build.ready then
                if condition then
                    build = ready
                end
            end

            return build.value
        end

        local function withFinalFalseWrite<T>(build: Build<T>, ready: ReadyBuild<T>): T
            if not build.ready then
                build = ready
                build = { ready = false }
            end

            return build.value
        end

        local function withLaterNestedWrite<T>(build: Build<T>, ready: ReadyBuild<T>, condition: boolean): T
            if not build.ready then
                build = ready
                if condition then
                    build = { ready = false }
                end
            end

            return build.value
        end

        local function afterCapturedWrite(): number
            local build: Build<number> = { ready = false }

            local function reset()
                build = { ready = false }
            end

            if not build.ready then
                build = { ready = true, value = 1 }
            end

            reset()
            return build.value
        end

        local function throughMutableAlias<T>(build: Build<T>, ready: ReadyBuild<T>): T
            local alias = build

            if not alias.ready then
                build = ready
            end

            return build.value
        end
    )");

    LUAU_REQUIRE_ERROR_COUNT(7, result);
    CHECK(get<MissingUnionProperty>(result.errors[0]));
    CHECK(get<MissingUnionProperty>(result.errors[1]));
    CHECK(get<MissingUnionProperty>(result.errors[2]));
    CHECK(get<MissingUnionProperty>(result.errors[3]));
    CHECK(get<MissingUnionProperty>(result.errors[4]));
    CHECK(get<MissingUnionProperty>(result.errors[5]));
    CHECK(get<MissingUnionProperty>(result.errors[6]));
}

TEST_SUITE_END();
