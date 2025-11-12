package test;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

class Material {
    String name;
    int quantity;

    public Material(String name, int quantity) {
        this.name = name;
        this.quantity = quantity;
    }

    @Override
    public String toString() {
        return name + " (Quantity: " + quantity + ")";
    }
}

class Bom {
    Map<String, List<Material>> bomData = new HashMap<>();

    public void addProduct(String productName, List<Material> materials) {
        bomData.put(productName, materials);
    }

    public List<Material> getMaterialsForProduct(String productName) {
        return bomData.getOrDefault(productName, new ArrayList<>());
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("BOM: \n");
        for (Map.Entry<String, List<Material>> e : bomData.entrySet()) {
            sb.append(e.getKey()).append(": ").append(e.getValue()).append("\n");
        }
        return sb.toString();
    }
}

class ProductionOrder {
    String productName;
    int quantity;

    public ProductionOrder(String productName, int quantity) {
        this.productName = productName;
        this.quantity = quantity;
    }

    @Override
    public String toString() {
        return "Production Order: " + productName + " (Quantity: " + quantity + ")";
    }
}

class Inventory {
    Map<String, Integer> materials = new HashMap<>();

    public void addMaterial(Material material) {
        materials.put(material.name, materials.getOrDefault(material.name, 0) + material.quantity);
    }

    public boolean checkMaterialAvailability(Bom bom, ProductionOrder order) {
        return checkMaterialAvailabilityRecursive(bom, order.productName, order.quantity);
    }

    private boolean checkMaterialAvailabilityRecursive(Bom bom, String productName, int quantity) {
        List<Material> materialsNeeded = bom.getMaterialsForProduct(productName);
        for (Material material : materialsNeeded) {
            int requiredQuantity = material.quantity * quantity;
            int availableQuantity = materials.getOrDefault(material.name, 0);

            if (availableQuantity < requiredQuantity) {
                // If current material is insufficient, recursively check material requirements of its subcomponents
                if (!(bom.getMaterialsForProduct(material.name).isEmpty()) &&
                        checkMaterialAvailabilityRecursive(bom, material.name, requiredQuantity - availableQuantity)) {
                    // If the material requirements of subcomponents can be met, consider the current material sufficient
                    continue;
                }
                System.out.println("Insufficient inventory: " + material.name);
                return false;
            }
        }
        return true;
    }

    public void consumeMaterials(Bom bom, ProductionOrder order) {
        List<Material> materialsNeeded = bom.getMaterialsForProduct(order.productName);
        for (Material material : materialsNeeded) {
            int requiredQuantity = material.quantity * order.quantity;
            int availableQuantity = materials.getOrDefault(material.name, 0);
            materials.put(material.name, availableQuantity - requiredQuantity);
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("Inventory: \n");
        for (Map.Entry<String, Integer> e : materials.entrySet()) {
            sb.append(e.getKey()).append(": ").append(e.getValue()).append("\n");
        }
        return sb.toString();
    }
}

public class test {
    public boolean testConflict(int time) throws InterruptedException {
        Bom bom = new Bom();
        bom.addProduct("Aluminum Alloy Sheet", List.of(
                new Material("Aluminum Alloy", 10)
        ));

        Inventory inventory = new Inventory();
        inventory.addMaterial(new Material("Aluminum Alloy", 10000));

        ProductionOrder order = new ProductionOrder("Aluminum Alloy Sheet", 2);

        Thread t1 = new Thread(() -> {
            for (int i = 0; i < time; i++) {
                inventory.consumeMaterials(bom, order);
            }
        });

        Thread t2 = new Thread(() -> {
            for (int i = 0; i < time; i++) {
                inventory.consumeMaterials(bom, order);
            }
        });

        t1.start();
        t2.start();

        t1.join();
        t2.join();

        System.out.println("Final count: " + inventory.materials.get("Aluminum Alloy"));
        return inventory.materials.get("Aluminum Alloy") == 10000 - 40 * time;
    }

    public static void main(String[] args) throws InterruptedException {
        test t = new test();
        int count = 0;
        for (int i = 0; i < 100; i++) {
            if (!t.testConflict(100)) {
                count++;
            }
        }

        System.out.println("Conflict count: " + count);
    }
}
