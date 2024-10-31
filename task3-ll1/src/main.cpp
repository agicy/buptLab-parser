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

namespace ll1_parser {

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
constexpr static size_t dollar = ~static_cast<size_t>(0);

class parser {
  private:
    using nid_t = size_t;
    using tid_t = size_t;
    using pid_t = size_t;

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
                assert(false);
            }
        }
    };

    enum class action_type_t {
        error,
        action,
    };

    struct action_t {
        action_type_t type;
        union id_t {
            pid_t pid;
        } id;
        action_t() : type(action_type_t::error), id() {}
        action_t(action_type_t type, size_t _id) : type(type) {
            switch (type) {
            case action_type_t::action:
                id.pid = _id;
                break;
            case action_type_t::error:
                id.pid = _id;
                break;
            default:
                assert(false);
            }
        }
    };

    class parser_table {
      private:
        std::unordered_map<nid_t, std::unordered_map<tid_t, action_t>> M;

      public:
        parser_table() {}
        auto insert(nid_t nid, tid_t tid, action_t action) -> void {
            assert(M[nid].find(tid) == M[nid].end());
            M[nid].insert(std::make_pair(tid, action));
        }
        auto is_empty(nid_t nid, tid_t tid) -> bool {
            return M[nid].find(tid) == M[nid].end();
        }
        auto query(nid_t nid, tid_t tid) -> action_t {
            assert(!is_empty(nid, tid));
            return M[nid][tid];
        }
    };

  private:
    grammar G;
    std::vector<std::pair<nid_t, std::vector<symbol_t>>> productions;
    std::unordered_map<nid_t, std::unordered_set<tid_t>> firsts;
    std::unordered_map<nid_t, std::unordered_set<tid_t>> follows;
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

    auto get_symbol_name(const symbol_t &symbol) -> std::string {
        switch (symbol.type) {
        case symbol_type_t::nonterminal:
            return G.N[symbol.symbol_id.nid];
        case symbol_type_t::terminal:
            return G.T[symbol.symbol_id.tid];
        default:
            assert(false);
            abort();
        }
    }

    auto get_token_name(const token_t &token) -> std::string {
        return token.attribute;
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

    auto set_firsts(void) -> void {
        auto can_be_empty = [&](const symbol_t &symbol) -> bool {
            if (symbol.type == symbol_type_t::terminal)
                return false;

            assert(symbol.type == symbol_type_t::nonterminal);
            const auto &first = firsts[symbol.symbol_id.nid];
            return first.find(epsilon) != first.end();
        };

        bool is_firsts_changed;
        do {
            is_firsts_changed = false;
            auto try_to_add_first = [&](const nid_t nid, const tid_t tid) -> void {
                if (firsts[nid].find(tid) == firsts[nid].end()) {
                    is_firsts_changed = true;
                    firsts[nid].insert(tid);
                }
            };

            for (const auto &production : productions) {
                const auto &lid = production.first;
                const auto &symbols = production.second;

                for (const auto &symbol : symbols) {
                    switch (symbol.type) {
                    case symbol_type_t::nonterminal: {
                        const auto &symbol_first = firsts[symbol.symbol_id.nid];
                        for (const tid_t tid : symbol_first)
                            if (tid != epsilon)
                                try_to_add_first(lid, tid);
                        break;
                    }
                    case symbol_type_t::terminal: {
                        try_to_add_first(lid, symbol.symbol_id.tid);
                        break;
                    }
                    }
                    if (!can_be_empty(symbol))
                        break;
                }

                if (std::all_of(symbols.begin(), symbols.end(), can_be_empty))
                    try_to_add_first(lid, epsilon);
            }
        } while (is_firsts_changed);
    }

    auto set_follows(void) -> void {
        auto can_be_empty = [&](const symbol_t &symbol) -> bool {
            if (symbol.type == symbol_type_t::terminal)
                return false;

            assert(symbol.type == symbol_type_t::nonterminal);
            const auto &first = firsts[symbol.symbol_id.nid];
            return first.find(epsilon) != first.end();
        };

        assert(get_symbol(G.S).type == symbol_type_t::nonterminal);
        follows[get_symbol(G.S).symbol_id.nid].insert(dollar);

        bool is_follows_changed;
        do {
            is_follows_changed = false;
            auto try_to_add_follow = [&](const nid_t nid, const tid_t tid) -> void {
                if (follows[nid].find(tid) == follows[nid].end()) {
                    is_follows_changed = true;
                    follows[nid].insert(tid);
                }
            };
            for (const auto &p : productions) {
                const auto &lid = p.first;
                const auto &symbols = p.second;
                for (auto it = symbols.begin(); it != symbols.end(); ++it) {
                    if (it->type == symbol_type_t::nonterminal) {
                        for (auto jt = it + 1; jt != symbols.end(); ++jt) {
                            switch (jt->type) {
                            case symbol_type_t::nonterminal: {
                                const auto &symbol_first = firsts.find(jt->symbol_id.nid)->second;
                                for (const tid_t tid : symbol_first)
                                    if (tid != epsilon)
                                        try_to_add_follow(it->symbol_id.nid, tid);
                                break;
                            }
                            case symbol_type_t::terminal: {
                                try_to_add_follow(it->symbol_id.nid, jt->symbol_id.tid);
                                break;
                            }
                            }
                            if (!can_be_empty(*jt))
                                break;
                        }
                        if (std::all_of(it + 1, symbols.end(), can_be_empty))
                            for (const auto &tid : follows[lid])
                                try_to_add_follow(it->symbol_id.nid, tid);
                    }
                }
            }
        } while (is_follows_changed);
    }

    auto set_parser_table() -> void {
        auto can_be_empty = [&](const symbol_t &symbol) -> bool {
            if (symbol.type == symbol_type_t::terminal)
                return false;

            assert(symbol.type == symbol_type_t::nonterminal);
            const auto &first = firsts[symbol.symbol_id.nid];
            return first.find(epsilon) != first.end();
        };

        for (pid_t pid = 0; pid < productions.size(); ++pid) {
            const auto &production = productions[pid];
            const auto &lid = production.first;
            const auto &symbols = production.second;
            for (const auto &symbol : symbols) {
                switch (symbol.type) {
                case symbol_type_t::nonterminal: {
                    const auto &symbol_first = firsts.find(symbol.symbol_id.nid)->second;
                    for (const tid_t tid : symbol_first)
                        if (tid != epsilon)
                            T.insert(lid, tid, action_t(action_type_t::action, pid));
                    break;
                }
                case symbol_type_t::terminal: {
                    T.insert(lid, symbol.symbol_id.tid, action_t(action_type_t::action, pid));
                    break;
                }
                }
                if (!can_be_empty(symbol))
                    break;
            }

            if (std::all_of(symbols.begin(), symbols.end(), can_be_empty))
                for (const auto &tid : follows[lid])
                    T.insert(lid, tid, action_t(action_type_t::action, pid));
        }
    }

  public:
    parser(const grammar &G) : G(G) {
        set_productions();
        set_firsts();
        set_follows();
        set_parser_table();
    }

  public:
    auto parse(std::unique_ptr<lexer> lexer) -> void {
        std::deque<symbol_t> S;
        S.push_back(get_symbol(G.S));
        std::deque<token_t> input;
        while (lexer->has_next())
            input.push_back(lexer->get_token());

        auto print_current_state = [&](void) -> void {
            std::printf("$");
            for (const auto &symbol : S)
                std::printf("%s", get_symbol_name(symbol).data());
            std::printf("\t");
            for (const auto &token : input)
                std::printf("%s", get_token_name(token).data());
            std::printf("$");
        };

        while (true) {
            print_current_state();
            std::printf("\t");

            auto token = input.front();

            if (token.token == "EOF" && S.empty()) {
                // accept

                std::printf("accept\n");
                break;
            }

            // parse
            if (S.empty()) {
                // error

                std::printf("error\n");
                break;
            }

            if (S.back().type == symbol_type_t::terminal) {
                assert(get_symbol(token.token).type == symbol_type_t::terminal);
                if (S.back().symbol_id.tid == get_symbol(token.token).symbol_id.tid) {
                    // match

                    input.pop_front(), S.pop_back();
                    std::printf("match\n");
                } else {
                    // error

                    std::printf("error\n");
                    break;
                }
            } else {
                assert(S.back().type == symbol_type_t::nonterminal);

                if (T.is_empty(
                        S.back().symbol_id.nid,
                        token.token != "EOF" ? get_symbol(token.token).symbol_id.tid : dollar)) {
                    // error

                    std::printf("error\n");
                    break;
                }

                const auto &action = T.query(
                    S.back().symbol_id.nid,
                    token.token != "EOF" ? get_symbol(token.token).symbol_id.tid : dollar);
                switch (action.type) {
                case action_type_t::action: {
                    // action

                    const auto &pid = action.id.pid;
                    const auto symbols = productions[pid].second;

                    S.pop_back();
                    for (auto it = symbols.rbegin(); it != symbols.rend(); ++it)
                        S.push_back(*it);

                    std::printf("%zu\n", pid + 1);
                    break;
                }

                default:
                    std::fprintf(stderr, "Unexpected action type\n");
                    abort();
                }
            }
        }
        return;
    }
};

} // namespace ll1_parser

int main() {
    ll1_parser::grammar G(
        std::vector<std::string>({
            "E",
            "T",
            "F",
            "A",
            "B",
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
            {"E", {"T", "A"}},
            {"A", {"+", "T", "A"}},
            {"A", {"-", "T", "A"}},
            {"A", {}},
            {"T", {"F", "B"}},
            {"B", {"*", "F", "B"}},
            {"B", {"/", "F", "B"}},
            {"B", {}},
            {"F", {"(", "E", ")"}},
            {"F", {"n"}},
        }),
        "E");

    auto parser = ll1_parser::parser(G);
    parser.parse(std::make_unique<lexer>(std::cin));

    return 0;
}
