pub fn collect_installed_products(
    product_ini_locations: &HashMap<String, String>,
) -> Result<Vec<Product>, anyhow::Error> {
    log::debug!("Entered collect_installed_products");
    let mut installed_products = Vec::with_capacity(product_ini_locations.len());

    for (product_name, product_ini_location) in product_ini_locations.iter() {
        // If ini file is not found, handle it and continue execution
        let product_result = add_product(product_name, product_ini_location);

        let installed_product = match product_result {
            Ok(product) => product,
            Err(error) => log::debug!("{}", error),
        };
        installed_products.push(installed_product);
    }
    
    Ok(installed_products)
}

![image](https://github.com/user-attachments/assets/e5f72ef3-2e4f-47d2-ad7a-7a28463c9438)
