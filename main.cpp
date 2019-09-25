#include <algorithm>
#include <iostream>
#include <cstddef>
#include <utility>
#include <numeric>
#include <fstream>
#include <chrono>
#include <vector>
#include <random>

#include <boost/graph/random.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/depth_first_search.hpp>
#include <boost/property_map/property_map.hpp>
#include <boost/sort/spreadsort/integer_sort.hpp>

namespace // TODO: an appropriate name
{

std::uint_fast64_t GenerateUniform() // TODO: better randomization, a dedicated class maybe
{
    static std::random_device         rd;
    static std::default_random_engine engine(rd());

    static std::uniform_int_distribution<std::uint_fast64_t> uniform;

    return uniform(engine);
}

template <template<class...> class Cont, class T>
void CountingSort(Cont<T>& from, Cont<T>& to, unsigned step) // TODO: Iterators as agrs
{
    static const auto offset = [](T num, unsigned step)
    {
        return std::size_t{ (num >> (step << 3)) & 0xFF };
    };

    std::array<std::size_t, 256> bucket = { 0 };

    for (const auto& n : from)
        ++bucket[offset(n, step)];

    std::partial_sum(bucket.begin(), bucket.end(), bucket.begin());

    for (auto it = from.rbegin(); it != from.rend(); ++it)
        to[--bucket[offset(*it, step)]] = *it;
}

template <template<class...> class Cont, class T>
void RadixSort(Cont<T>& input) // TODO: Iterators as agrs
{
    Cont<T> buffer(input.size());

    Cont<T>* from = &input;
    Cont<T>* to   = &buffer;

    for (auto step = 0; step < sizeof(std::size_t); ++step)
    {
        CountingSort(*from, *to, step);

        std::swap(from, to);
    }
}

} // namespace

namespace BridgeFindingAlgoritms
{

template <class G> using V = typename boost::graph_traits<G>::vertex_descriptor;
template <class G> using E = typename boost::graph_traits<G>::edge_descriptor;

using Edge = std::pair<std::size_t, std::size_t>;

struct DFS_VisitorBase
{
    template <class G> void initialize_vertex(V<G>, const G&) {}
    template <class G> void start_vertex(V<G>, const G&) {}
    template <class G> void discover_vertex(V<G>, const G&) {}
    template <class G> void finish_vertex(V<G>, const G&) {}
    template <class G> void examine_edge(E<G>, const G&) {}
    template <class G> void tree_edge(E<G>, const G&) {}
    template <class G> void back_edge(E<G>, const G&) {}
    template <class G> void forward_or_cross_edge(E<G>, const G&) {}
    template <class G> void finish_edge(E<G>, const G&) {}
};

template <class V_IdMap>
class BridgeFindingVisitor
    : public DFS_VisitorBase
{
public:
    BridgeFindingVisitor(const V_IdMap& vertices_ids, std::vector<Edge>& out_bridges)
        : m_bridges(out_bridges)
        , m_vertices_ids(vertices_ids)
        , m_timer(0)
        , m_first_run(true)
    {}

    template <class G>
    void start_vertex(V<G> s, const G& g)
    {
        if (m_first_run)
        {
            m_vertices_info.resize(boost::num_vertices(g));
            m_first_run = false;
        }

        const auto start_id = GetId(s);
        m_vertices_info[start_id].parent_id = start_id; // root vertex is its own parent

        m_timer = 0;
    }

    template <class G>
    void discover_vertex(V<G> v, const G&)
    {
        ++m_timer;

        const auto v_id = GetId(v);
        m_vertices_info[v_id].time_discovered = m_timer;
        m_vertices_info[v_id].time_minimal    = m_timer;
    }

    template <class G>
    void tree_edge(E<G> e, const G&)
    {
        m_vertices_info[GetId(e.m_target)].parent_id = GetId(e.m_source);
    }

    template <class G>
    void back_edge(E<G> e, const G&)
    {
        const auto& target_info = m_vertices_info[GetId(e.m_target)]; // vertex that the edge is pointing to
        auto&       source_info = m_vertices_info[GetId(e.m_source)]; // vertex that the edge is coming from

        if (GetId(e.m_target) == source_info.parent_id)
            return; /* Disambiguate between tree and back egdes.       *
                     * If a target edge is actually a source's parent, *
                     * then it, in fact, is a tree edge                */

        source_info.time_minimal = std::min(source_info.time_minimal,
                                            target_info.time_discovered);
    }

    template <class G>
    void finish_vertex(V<G> v, const G&)
    {
        const auto v_id = GetId(v);
        const auto p_id = m_vertices_info[v_id].parent_id;

        const auto& vertex_info = m_vertices_info[v_id];
        auto&       parent_info = m_vertices_info[p_id];

        if (parent_info.time_discovered < vertex_info.time_minimal)
        {
            // <v, p> is a bridge!

            m_bridges.emplace_back(p_id, v_id);
        }

        parent_info.time_minimal = std::min(parent_info.time_minimal,
                                            vertex_info.time_minimal);
    }

private:
    std::vector<Edge>& m_bridges;

    struct VertexInfo
    {
        std::size_t parent_id;

        std::size_t time_discovered;
        std::size_t time_minimal;
    };

    std::vector<VertexInfo> m_vertices_info;

    std::size_t m_timer;

    bool m_first_run;

    const V_IdMap& m_vertices_ids;

    std::size_t GetId(const typename V_IdMap::key_type& v) const
    {
        return m_vertices_ids[v];
    }
};

template <class G>
std::vector<Edge> FindBridges(const G& g)
{
    std::vector<Edge> bridges;

    BridgeFindingVisitor find_bridges(boost::get(boost::vertex_index, g), bridges);
    boost::depth_first_search(g, boost::visitor(find_bridges));

    return bridges;
}

struct EdgeBitmask
{
    Edge               edge;
    std::uint_fast64_t bitmask;

    operator std::uint_fast64_t() const { return bitmask; }
};

template <class V_IdMap, class E_IdMap>
class BitmaskSettingVisitor
    : public DFS_VisitorBase
{
public:
    BitmaskSettingVisitor
    (
        const V_IdMap& vertices_ids,
        const E_IdMap& edges_ids,

        std::vector<Edge>*        out_one_bridges = nullptr,
        std::vector<EdgeBitmask>* out_edges_bitmasks = nullptr
    )
        : m_vertices_ids(vertices_ids)
        , m_edges_ids(edges_ids)

        , m_one_bridges(out_one_bridges)
        , m_edges_bitmasks(out_edges_bitmasks)

        , m_is_first_run(true)
    {}

    template <class G>
    void start_vertex(V<G> s, const G& g)
    {
        if (m_is_first_run)
        {
            m_vertices_info.resize(boost::num_vertices(g));
            m_edges_info.resize(boost::num_edges(g));

            if (m_edges_bitmasks != nullptr)
                m_edges_bitmasks->resize(boost::num_edges(g));

            m_is_first_run = false;
        }

        const auto start_id = GetId(s);
        m_vertices_info[start_id].parent_id = start_id;
    }

    template <class G>
    void discover_vertex(V<G> v, const G&)
    {
        m_vertices_info[GetId(v)].bitmask = 0;
    }

    template <class G>
    void tree_edge(E<G> e, const G&)
    {
        m_vertices_info[GetId(e.m_target)].parent_id = GetId(e.m_source);
    }

    template <class G>
    void back_edge(E<G> e, const G&)
    {
        const auto [e_id, source_id, target_id] = GetIds(e);

        if (m_vertices_info[source_id].parent_id == target_id)
            return;

        const auto bitmask = GenerateUniform();

        m_edges_info[e_id].bitmask         ^= bitmask;
        m_vertices_info[source_id].bitmask ^= bitmask;
        m_vertices_info[target_id].bitmask ^= bitmask;

        if (m_edges_bitmasks != nullptr)
            (*m_edges_bitmasks)[e_id] = { { source_id, target_id }, bitmask };
    }

    template <class G>
    void finish_edge(E<G> e, const G&)
    {
        const auto [e_id, source_id, target_id] = GetIds(e);

        if (m_vertices_info[target_id].parent_id != source_id)
            return; // magic

        const auto bitmask = m_vertices_info[target_id].bitmask;

        m_edges_info[e_id].bitmask         ^= bitmask;
        m_vertices_info[source_id].bitmask ^= bitmask;

        if (bitmask == 0 && m_one_bridges != nullptr)
            m_one_bridges->emplace_back(source_id, target_id);

        if (m_edges_bitmasks != nullptr)
            (*m_edges_bitmasks)[e_id] = { { source_id, target_id }, bitmask };
    }

private:
    struct VertexInfo
    {
        std::size_t parent_id;

        std::uint_fast64_t bitmask;
    };

    struct EdgeInfo
    {
        std::uint_fast64_t bitmask;
    };

    std::vector<Edge>*        m_one_bridges;
    std::vector<EdgeBitmask>* m_edges_bitmasks;

    std::vector<VertexInfo> m_vertices_info;
    std::vector<EdgeInfo>   m_edges_info;

    bool m_is_first_run;

    const V_IdMap& m_vertices_ids;
    const E_IdMap& m_edges_ids;

    std::size_t GetId(const typename V_IdMap::key_type& v) const
    {
        return m_vertices_ids[v];
    }

    std::size_t GetId(const typename E_IdMap::key_type& e) const
    {
        return m_edges_ids[e];
    }

    std::tuple<std::size_t, std::size_t, std::size_t>
        GetIds(const typename E_IdMap::key_type& e) const
    {
        return { m_edges_ids[e], m_vertices_ids[e.m_source], m_vertices_ids[e.m_target] };
    }
};

template <class G, class E_IdMap>
std::vector<Edge> RandFindBridges(const G& g, const E_IdMap& edges_indices)
{
    std::vector<Edge> bridges;

    BitmaskSettingVisitor rand_find_bridges
    (
        boost::get(boost::vertex_index, g),
        edges_indices,

        &bridges
    );
    boost::depth_first_search(g, boost::visitor(rand_find_bridges));

    return bridges;
}

template <class G, class E_IdMap>
std::vector<std::vector<EdgeBitmask>> RandFind2Bridges(const G& g, const E_IdMap& edges_indices)
{
    std::vector<EdgeBitmask> edges_bitmasks;

    BitmaskSettingVisitor calculate_bitmasks
    (
        boost::get(boost::vertex_index, g),
        edges_indices,

        nullptr,
        &edges_bitmasks
    );
    boost::depth_first_search(g, boost::visitor(calculate_bitmasks));

    RadixSort(edges_bitmasks);
    //boost::sort::spreadsort::integer_sort(edges_bitmasks.begin(), edges_bitmasks.end());

    std::vector<std::vector<EdgeBitmask>> two_bridges_ranges;

    for (auto start = edges_bitmasks.begin(); start != edges_bitmasks.end(); ":^)")
    {
        auto range = std::equal_range(start, edges_bitmasks.end(), *start);

        if (std::distance(range.first, range.second) > 1)
            two_bridges_ranges.emplace_back(range.first, range.second);

        start = range.second;
    }

    return two_bridges_ranges;
}

} // namespace BridgeFindingAlgoritms

template <class G>
void RandomizeGraph(std::size_t num_v, std::size_t num_e, G& g) // TODO: refactor
{
    static std::random_device rd;

    std::default_random_engine engine(rd());

    boost::generate_random_graph(g, num_v, num_e, engine, false);
}

void PerformanceTests()
{
    using Graph = boost::adjacency_list
    <
        boost::vecS,
        boost::vecS,
        boost::undirectedS,
        boost::no_property,
        boost::property<boost::edge_index_t, std::size_t>
    >;

    std::ofstream one_non_rand_perf("1-bridges-non-rand-perf-tests.txt");
    std::ofstream one_rand_perf("1-bridges-rand-perf-tests.txt");
    std::ofstream two_rand_perf("2-bridges-rand-perf-tests.txt");

    for (std::size_t size = 10'000; size <= 1'000'000; size += 10'000)
    {
        Graph g;
        RandomizeGraph(size, size, g);

        auto edges_indices = boost::get(boost::edge_index, g);
        const auto fill_edge_indices = [&edges_indices, i = std::size_t()](const auto& edge) mutable
        {
            edges_indices[edge] = i++;
        };
        std::for_each(boost::edges(g).first, boost::edges(g).second, fill_edge_indices);
        
        {
            auto start = std::chrono::system_clock::now();
            BridgeFindingAlgoritms::FindBridges(g);
            auto end   = std::chrono::system_clock::now();

            auto duration = std::chrono::duration<double>(end - start).count();
            one_non_rand_perf << size     << ' ';
            one_non_rand_perf << duration << '\n';
        }

        {
            auto start = std::chrono::system_clock::now();
            BridgeFindingAlgoritms::RandFindBridges(g, edges_indices);
            auto end   = std::chrono::system_clock::now();

            auto duration = std::chrono::duration<double>(end - start).count();
            one_rand_perf << size     << ' ';
            one_rand_perf << duration << '\n';
        }

        {
            auto start = std::chrono::system_clock::now();
            BridgeFindingAlgoritms::RandFind2Bridges(g, edges_indices);
            auto end   = std::chrono::system_clock::now();

            auto duration = std::chrono::duration<double>(end - start).count();
            two_rand_perf << size     << ' ';
            two_rand_perf << duration << '\n';
        }
    }
}

template <class G>
void FillGraph(G& g) // TODO: more examples
{
    boost::add_edge(0, 1, g); /* A GRAPH ON 7 VERTICES */
    boost::add_edge(0, 4, g); /*                       */
    boost::add_edge(1, 2, g); /*           2\          */
    boost::add_edge(1, 3, g); /*          /|\ \        */
    boost::add_edge(1, 4, g); /*         / | \  \      */
    boost::add_edge(2, 3, g); /*        /  |  \   \    */
    boost::add_edge(2, 5, g); /*   0---1---3---5---6   */
    boost::add_edge(2, 6, g); /*    \   \  |  /        */
    boost::add_edge(3, 4, g); /*      \  \ | /         */
    boost::add_edge(3, 5, g); /*        \ \|/          */
    boost::add_edge(4, 5, g); /*          \4           */
    boost::add_edge(5, 6, g); /*                       */
}

void AccuracyTest()
{
    using Graph = boost::adjacency_list
    <
        boost::vecS,
        boost::vecS,
        boost::undirectedS,
        boost::no_property,
        boost::property<boost::edge_index_t, std::size_t>
    >;

    Graph g;
    FillGraph(g);

    auto edges_indices = boost::get(boost::edge_index, g);
    const auto fill_edge_indices = [&edges_indices, i = std::size_t()](const auto& edge) mutable
    {
        edges_indices[edge] = i++;
    };
    std::for_each(boost::edges(g).first, boost::edges(g).second, fill_edge_indices);

    auto bridges      = BridgeFindingAlgoritms::FindBridges(g);
    auto bridges_rand = BridgeFindingAlgoritms::RandFindBridges(g, edges_indices);

    if (bridges.empty() && bridges_rand.empty())
        std::cout << "NO 1-BRIDGES" << std::endl;
    
    else if (bridges.size() != bridges_rand.size())
        std::cout << "SIZE MISMATCH" << std::endl;
    
    else if (!std::is_permutation(bridges.begin(), bridges.end(), bridges_rand.begin()))
        std::cout << "EDGES MISMATCH" << std::endl;
    
    else
    {
        std::cout << "PASS"       << std::endl;
        std::cout << "1-bridges:" << std::endl;

        for (auto bridge : bridges)
            std::cout << bridge.first << " - " << bridge.second << std::endl;
    }

    auto two_bridges_ranges = BridgeFindingAlgoritms::RandFind2Bridges(g, edges_indices);

    std::size_t i = 0;
    for (const auto& range : two_bridges_ranges)
    {
        std::cout << "range " << i++ << ":\n";
    
        for (const auto& two_bridge : range)
            std::cout << '\t' << two_bridge.edge.first << " - " << two_bridge.edge.second << std::endl;
    }
}

int main()
{
    //PerformanceTests();
    AccuracyTest();
}
