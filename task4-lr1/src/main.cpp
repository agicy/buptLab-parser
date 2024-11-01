#include <algorithm>
#include <cassert>
#include <iostream>
#include <memory>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <vector>

struct token_t {
    std::string token;
    std::string attribute;
    token_t(const std::string &token, const std::string &attribute) : token(token), attribute(attribute) {}
    auto to_string() const -> std::string {
        using namespace std::string_literals;
        return "<"s + token + ","s + attribute + ">"s;
    }
};

class lexer {
  private:
    std::reference_wrapper<std::istream> input;

  public:
    lexer(std::istream &input) : input(std::reference_wrapper<std::istream>(input)) {}
    auto has_next(void) -> bool {
        return !input.get().eof();
    }
    auto get_token(void) -> token_t {
        int c;
        do
            c = input.get().get();
        while (isspace(c));

        if (c == EOF)
            return token_t("EOF", "");

        switch (c) {
        case '+':
            return token_t("+", "+");
        case '-':
            return token_t("-", "-");
        case '*':
            return token_t("*", "*");
        case '/':
            return token_t("/", "/");
        case 'n':
            return token_t("n", "n");
        case '(':
            return token_t("(", "(");
        case ')':
            return token_t(")", ")");
        default:
            std::fprintf(stderr, "Lexer get unexpected c = %d\n", c);
            abort();
        }
    }
};

namespace lr1_parser {

struct grammar {
    std::vector<std::string> N;
    std::vector<std::string> T;
    std::vector<std::pair<std::string, std::vector<std::string>>> P;
    std::string S;
    grammar(
        const std::vector<std::string> &N,
        const std::vector<std::string> &T,
        const std::vector<std::pair<std::string, std::vector<std::string>>> &P,
        const std::string &S)
        : N(N), T(T), P(P), S(S) {}
};

constexpr static size_t epsilon = ~static_cast<size_t>(0);
constexpr static size_t dollar = (~static_cast<size_t>(0)) ^ 1;

class parser {
  private:
    using nid_t = size_t;
    using tid_t = size_t;
    using pid_t = size_t;
    using sid_t = size_t;

    enum class symbol_type_t {
        nonterminal,
        terminal,
    };

    struct symbol_t {
        symbol_type_t type;
        union symbol_id_t {
            nid_t nid;
            tid_t tid;
        } symbol_id;

        symbol_t(symbol_type_t type, size_t id) : type(type) {
            switch (type) {
            case symbol_type_t::nonterminal:
                symbol_id.nid = id;
                break;
            case symbol_type_t::terminal:
                symbol_id.tid = id;
                break;
            default:
                std::fprintf(stderr, "Unexpected symbol type");
                abort();
            }
        }

        bool operator==(const symbol_t &another) const {
            if (type != another.type)
                return false;

            switch (type) {
            case symbol_type_t::nonterminal:
                return symbol_id.nid == another.symbol_id.nid;
            case symbol_type_t::terminal:
                return symbol_id.tid == another.symbol_id.tid;
            default:
                std::fprintf(stderr, "Unexpected symbol type");
                abort();
            }
        }
    };

    struct symbol_t_hash {
        size_t operator()(const symbol_t &symbol) const {
            switch (symbol.type) {
            case symbol_type_t::nonterminal:
                return std::hash<size_t>()(symbol.symbol_id.nid);
            case symbol_type_t::terminal:
                return std::hash<size_t>()(symbol.symbol_id.tid);
            default:
                std::fprintf(stderr, "Unexpected symbol type");
                abort();
            }
        }
    };

    struct lr_item {
        pid_t pid;
        size_t position;
        tid_t follow;
        lr_item() {}
        lr_item(pid_t pid, size_t position, tid_t follow) : pid(pid), position(position), follow(follow) {}
        bool operator==(const lr_item &another) const {
            return pid == another.pid &&
                   position == another.position &&
                   follow == another.follow;
        }
    };

    struct lr_item_hash {
        size_t operator()(const lr_item &item) const {
            return std::hash<pid_t>()(item.pid) ^
                   std::hash<size_t>()(item.position) ^
                   std::hash<tid_t>()(item.follow);
        }
    };

    enum class action_type_t {
        error,
        shift,
        reduce,
        accept,
    };

    struct action_t {
        action_type_t type;
        union id_t {
            sid_t sid; // shift to state sid
            pid_t pid; // reduce by production pid
        } id;
        action_t() : type(action_type_t::error), id() {}
        action_t(action_type_t type) : type(type), id() {}
        action_t(action_type_t type, size_t _id) : type(type) {
            switch (type) {
            case action_type_t::shift:
                id.sid = _id;
                break;
            case action_type_t::reduce:
                id.pid = _id;
                break;
            default:
                std::fprintf(stderr, "Unexpected action type when constructing action");
                abort();
            }
        }
        bool operator!=(const action_t &another) const {
            if (type != another.type)
                return true;

            switch (type) {
            case action_type_t::error:
                return true;
            case action_type_t::accept:
                return true;
            case action_type_t::shift:
                return id.sid != another.id.sid;
            case action_type_t::reduce:
                return id.pid != another.id.pid;
            default:
                std::fprintf(stderr, "Unexpected action type when constructing action");
                abort();
            }
        }
    };

    class parser_table {
      private:
        std::unordered_map<sid_t, std::unordered_map<tid_t, action_t>> _action;
        std::unordered_map<sid_t, std::unordered_map<nid_t, sid_t>> _goto;

      public:
        parser_table() {}
        auto insert_action(sid_t sid, tid_t tid, action_t action) -> void {
            if (_action[sid].find(tid) != _action[sid].end() && _action[sid][tid] != action) {
                std::fprintf(
                    stderr,
                    "Parser table failed when insert action, more then one action inserted\n");
                abort();
            }
            _action[sid].insert(std::make_pair(tid, action));
        }

        auto is_action_empty(sid_t sid, tid_t tid) -> bool {
            return _action[sid].find(tid) == _action[sid].end();
        }

        auto query_action(sid_t sid, tid_t tid) -> action_t {
            if (!is_action_empty(sid, tid))
                return _action[sid][tid];
            else
                return action_t(action_type_t::error);
        }

        auto insert_goto(sid_t state_id, nid_t nid, sid_t next_state_id) -> void {
            if (_goto[state_id].find(nid) != _goto[state_id].end() && _goto[state_id][nid] != next_state_id) {
                std::fprintf(
                    stderr,
                    "Parser table failed when insert goto, more then one goto inserted\n");
                abort();
            }
            _goto[state_id][nid] = next_state_id;
        }

        auto is_goto_empty(sid_t state_id, nid_t nid) -> bool {
            return _goto[state_id].find(nid) == _goto[state_id].end();
        }

        auto query_goto(sid_t state_id, nid_t nid) -> sid_t {
            assert(!is_goto_empty(state_id, nid));
            return _goto[state_id][nid];
        }
    };

  private:
    grammar G;
    std::vector<std::pair<nid_t, std::vector<symbol_t>>> productions;
    std::unordered_map<nid_t, std::unordered_set<tid_t>> firsts;
    std::vector<std::unordered_set<lr_item, lr_item_hash>> states;
    std::unordered_map<sid_t, std::unordered_map<symbol_t, sid_t, symbol_t_hash>> transitions;
    parser_table T;

  private:
    auto get_symbol(const std::string &s) -> symbol_t {
        auto nit = std::find(G.N.begin(), G.N.end(), s);
        auto tit = std::find(G.T.begin(), G.T.end(), s);

        if (nit != G.N.end() && tit == G.T.end()) {
            nid_t nid = nit - G.N.begin();
            return symbol_t(symbol_type_t::nonterminal, nid);
        }

        if (nit == G.N.end() && tit != G.T.end()) {
            tid_t tid = tit - G.T.begin();
            return symbol_t(symbol_type_t::terminal, tid);
        }

        std::fprintf(stderr, "Unexpected symbol name = %s\n", s.data());
        abort();
    }

    auto set_productions(void) -> void {
        for (const auto &p : G.P) {
            auto lit = std::find(G.N.begin(), G.N.end(), p.first);
            assert(lit != G.N.end());
            nid_t lid = lit - G.N.begin();

            std::vector<symbol_t> symbols;
            for (const auto &s : p.second)
                symbols.push_back(get_symbol(s));

            productions.emplace_back(lid, symbols);
        }
        return;
    }

    auto get_symbol_first(const symbol_t &symbol) -> std::unordered_set<tid_t> {
        switch (symbol.type) {
        case symbol_type_t::nonterminal:
            return firsts[symbol.symbol_id.nid];
        case symbol_type_t::terminal:
            return {symbol.symbol_id.tid};
        default:
            std::fprintf(stderr, "Unexpected symbol type\n");
            abort();
        }
    }

    auto get_first(const std::vector<symbol_t> symbols) -> std::unordered_set<tid_t> {
        auto can_be_empty = [&](const symbol_t &symbol) -> bool {
            if (symbol.type == symbol_type_t::terminal)
                return false;

            assert(symbol.type == symbol_type_t::nonterminal);
            const auto &first = firsts[symbol.symbol_id.nid];
            return first.find(epsilon) != first.end();
        };

        std::unordered_set<tid_t> result;
        for (const auto &symbol : symbols) {
            for (const auto &tid : get_symbol_first(symbol))
                if (tid != epsilon)
                    result.insert(tid);
            if (!can_be_empty(symbol))
                break;
        }
        if (std::all_of(symbols.begin(), symbols.end(), can_be_empty))
            result.insert(epsilon);
        return result;
    }

    auto set_firsts(void) -> void {
        bool is_firsts_changed;
        auto try_to_add_first = [&](const nid_t nid, const tid_t tid) -> void {
            if (firsts[nid].find(tid) == firsts[nid].end()) {
                is_firsts_changed = true;
                firsts[nid].insert(tid);
            }
        };

        do {
            is_firsts_changed = false;

            for (const auto &production : productions) {
                const auto &lid = production.first;
                const auto &symbols = production.second;

                for (const auto &tid : get_first(symbols))
                    try_to_add_first(lid, tid);
            }
        } while (is_firsts_changed);
    }

    auto get_closure(std::unordered_set<lr_item, lr_item_hash> items) -> std::unordered_set<lr_item, lr_item_hash> {
        std::unordered_set<lr_item, lr_item_hash> tmp;
        do {
            tmp = items;
            for (const auto &item : tmp) {
                const auto &production = productions[item.pid];
                const auto &symbols = production.second;

                if (item.position == symbols.size())
                    continue;
                if (symbols[item.position].type == symbol_type_t::terminal)
                    continue;

                const auto &extend_nid = symbols[item.position].symbol_id.nid;
                std::vector<symbol_t> follow_symbols;
                for (size_t i = item.position + 1; i < symbols.size(); ++i)
                    follow_symbols.push_back(symbols[i]);
                follow_symbols.push_back(symbol_t(symbol_type_t::terminal, item.follow));

                assert(!follow_symbols.empty());

                for (pid_t pid = 0; pid < productions.size(); ++pid) {
                    const auto &another_production = productions[pid];
                    const auto &another_lid = another_production.first;

                    if (another_lid == extend_nid)
                        for (const auto &tid : get_first(follow_symbols))
                            items.insert(lr_item(pid, 0, tid));
                }
            }
        } while (items != tmp);
        return items;
    }

    auto forward_symbol(const std::unordered_set<lr_item, lr_item_hash> &items, const symbol_t &symbol) -> std::unordered_set<lr_item, lr_item_hash> {
        std::unordered_set<lr_item, lr_item_hash> result;
        for (const auto &item : items) {
            const auto &production = productions[item.pid];
            const auto &symbols = production.second;

            if (item.position == symbols.size())
                continue;

            if (symbols[item.position] == symbol)
                result.insert(lr_item(item.pid, item.position + 1, item.follow));
        }
        return result;
    }

    using state_t = std::unordered_set<lr_item, lr_item_hash>;

    auto get_state_id(const state_t &state) -> sid_t {
        auto it = std::find(states.begin(), states.end(), state);
        assert(it != states.end());
        return it - states.begin();
    }

    auto set_dfa(void) -> void {
        states.push_back(get_closure({lr_item(0, 0, dollar)}));

        std::vector<symbol_t> symbols;
        for (nid_t nid = 0; nid < G.N.size(); ++nid)
            symbols.push_back(symbol_t(symbol_type_t::nonterminal, nid));
        for (tid_t tid = 0; tid < G.T.size(); ++tid)
            symbols.push_back(symbol_t(symbol_type_t::terminal, tid));

        for (sid_t sid = 0; sid < states.size(); ++sid) {
            auto state = states[sid];
            for (const auto &symbol : symbols) {
                auto result = get_closure(forward_symbol(state, symbol));
                if (!result.empty()) {
                    if (std::find(states.begin(), states.end(), result) == states.end())
                        states.push_back(result);

                    assert(transitions[sid].find(symbol) == transitions[sid].end());
                    transitions[sid][symbol] = get_state_id(result);
                }
            }
        }
    }

    auto set_parser_table(void) -> void {
        for (sid_t sid = 0; sid < states.size(); ++sid) {
            const auto &state = states[sid];
            for (const auto &item : state) {
                if (item.pid == 0 && item.follow == dollar && productions[item.pid].second.size() == item.position) {
                    T.insert_action(sid, dollar, action_t(action_type_t::accept));
                    continue;
                }
                if (item.position == productions[item.pid].second.size()) {
                    T.insert_action(sid, item.follow, action_t(action_type_t::reduce, item.pid));
                    continue;
                }
                if (productions[item.pid].second[item.position].type == symbol_type_t::terminal) {
                    auto it = transitions[sid].find(productions[item.pid].second[item.position]);
                    assert(it != transitions[sid].end());

                    T.insert_action(
                        sid,
                        productions[item.pid].second[item.position].symbol_id.tid,
                        action_t(action_type_t::shift, it->second));
                    continue;
                }
                if (productions[item.pid].second[item.position].type == symbol_type_t::nonterminal) {
                    auto it = transitions[sid].find(productions[item.pid].second[item.position]);
                    assert(it != transitions[sid].end());

                    T.insert_goto(
                        sid,
                        productions[item.pid].second[item.position].symbol_id.nid,
                        it->second);
                    continue;
                }
            }
        }
    }

  public:
    parser(const grammar &G) : G(G) {
        set_productions();
        set_firsts();
        set_dfa();
        set_parser_table();
    }

  public:
    auto parse(std::unique_ptr<lexer> lexer) -> void {
        std::deque<sid_t> S;
        S.push_back(0);
        std::deque<symbol_t> help_symbol;

        std::deque<token_t> input;
        while (lexer->has_next())
            input.push_back(lexer->get_token());

        while (true) {
            auto token = input.front();
            auto symbol = token.token != "EOF" ? get_symbol(token.token) : symbol_t(symbol_type_t::terminal, dollar);

            assert(symbol.type == symbol_type_t::terminal);
            auto action = T.query_action(S.back(), symbol.symbol_id.tid);

            switch (action.type) {
            case action_type_t::accept: {
                std::printf("accept\n");
                return;
            }
            case action_type_t::shift: {
                std::printf("shift\n");
                S.push_back(action.id.sid);
                help_symbol.push_back(symbol_t(symbol_type_t::terminal, symbol.symbol_id.tid));

                input.pop_front();
                break;
            }
            case action_type_t::reduce: {
                std::printf("%zu\n", action.id.pid);

                const auto &production = productions[action.id.pid];
                const auto &nonterminal = production.first;
                const auto &symbols = production.second;
                for (size_t i = 0; i < symbols.size(); ++i) {
                    assert(!S.empty());
                    S.pop_back();
                    help_symbol.pop_back();
                }

                if (T.is_goto_empty(S.back(), nonterminal)) {
                    std::printf("error\n");
                    return;
                }

                auto next_state = T.query_goto(S.back(), nonterminal);
                S.push_back(next_state);
                help_symbol.push_back(symbol_t(symbol_type_t::nonterminal, nonterminal));
                break;
            }
            case action_type_t::error: {
                std::printf("error\n");
                return;
            }
            }
        }
        return;
    }
};

} // namespace lr1_parser

int main() {
    lr1_parser::grammar G(
        std::vector<std::string>({
            "E'",
            "E",
            "T",
            "F",
        }),
        std::vector<std::string>({
            "+",
            "-",
            "*",
            "/",
            "(",
            ")",
            "n",
        }),
        std::vector<std::pair<std::string, std::vector<std::string>>>({
            {"E'", {"E"}},
            {"E", {"E", "+", "T"}},
            {"E", {"E", "-", "T"}},
            {"E", {"T"}},
            {"T", {"T", "*", "F"}},
            {"T", {"T", "/", "F"}},
            {"T", {"F"}},
            {"F", {"(", "E", ")"}},
            {"F", {"n"}},
        }),
        "E'");

    auto parser = lr1_parser::parser(G);
    parser.parse(std::make_unique<lexer>(std::cin));

    return 0;
}
