#include "layout_cli.h"
#include "queue_orders.h"

void testLayouts(CMDOptions& options);

int main(int argc, char* argv[]) {
  LayoutCLI cli;
  cli.name = "planar_queues";
  cli.options = [](CMDOptions& o) {
    o.registerOption("-queues", "33", "Queue bound: 33, 48, or 49 (alias for 48)");
    for (const char* bound : {"33", "48", "49"}) o.registerAllowedValue("-queues", bound);
  };
  cli.pageBound = [](const CMDOptions& o) { return o.getInt("-queues") == 49 ? 48 : o.getInt("-queues"); };
  cli.format = [](const CMDOptions& o) { return "pps" + o.getStr("-queues"); };
  cli.build = [](PlanarGraph& g, CMDOptions& o, std::vector<int>& order, std::map<EdgeTy, int>& pages) {
    buildPPSLayout(g, o.getInt("-queues") == 49 ? 48 : o.getInt("-queues"), order, pages, o.getInt("-verbose"));
  };
  cli.statistics = [](const std::vector<EdgeTy>& edges, const std::vector<int>& order) {
    std::cerr << "max-rainbow: " << countRainbow(edges, order) << "\n";
  };
  cli.test = testLayouts;
  return runLayoutCLI(argc, argv, cli);
}
