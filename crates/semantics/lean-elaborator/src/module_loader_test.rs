#[cfg(test)]
mod module_loader_integration_tests {
    use super::*;
    use crate::{
        environment_ext::init_basic_environment,
        module_loader::{ModuleLoader, ModuleLoaderConfig},
        Elaborator,
    };
    use lean_kernel::Name;
    use std::path::PathBuf;

    #[test]
    fn test_module_loading_with_real_files() {
        // Create module loader with test modules directory
        let mut config = ModuleLoaderConfig::default();
        // Use absolute path to ensure we find the test modules
        // The test modules are in the project root, not in the crate directory
        let crate_dir = std::env::current_dir().unwrap();
        let project_root = crate_dir.parent().unwrap().parent().unwrap().parent().unwrap();
        config.search_paths.push(project_root.join("test/modules"));

        let loader = ModuleLoader::new(config.clone());

        // Test finding a module
        let module_name = Name::str(Name::str(Name::mk_simple("Foo"), "Bar"), "Baz");
        let module_path = loader.find_module(&module_name);
        if let Err(e) = &module_path {
            eprintln!("Failed to find module: {:?}", e);
            eprintln!("Search paths: {:?}", config.search_paths);
            eprintln!("Current dir: {:?}", std::env::current_dir());
        }
        assert!(module_path.is_ok());
        assert!(module_path.unwrap().ends_with("Foo/Bar/Baz.lean"));

        // Test loading a module
        let (module, syntax) = loader.load_module(&module_name).unwrap();
        assert_eq!(module.name, module_name);
        assert!(module.imports.is_empty()); // Baz has no imports

        // Test module with imports
        let basic_name = Name::str(Name::mk_simple("Foo"), "Basic");
        let (basic_module, _) = loader.load_module(&basic_name).unwrap();
        assert_eq!(basic_module.imports.len(), 1);
        assert_eq!(basic_module.imports[0].module, module_name);
    }

    #[test]
    fn test_module_elaboration_with_dependencies() {
        // Create module loader with test modules directory
        let mut config = ModuleLoaderConfig::default();
        // Use absolute path to ensure we find the test modules
        // The test modules are in the project root, not in the crate directory
        let crate_dir = std::env::current_dir().unwrap();
        let project_root = crate_dir.parent().unwrap().parent().unwrap().parent().unwrap();
        config.search_paths.push(project_root.join("test/modules"));

        let loader = ModuleLoader::new(config.clone());
        let base_env = init_basic_environment();

        // Elaborate Foo.Bar.Baz first
        let baz_name = Name::str(Name::str(Name::mk_simple("Foo"), "Bar"), "Baz");
        let baz_env = loader.elaborate_module(&baz_name, base_env.clone());
        assert!(baz_env.is_ok());

        // Check that definitions from Baz are in the environment
        let baz_env = baz_env.unwrap();
        let hello_name = Name::str(baz_name.clone(), "hello");
        assert!(baz_env.contains(&hello_name));

        // Elaborate Foo.Basic which imports Baz
        let basic_name = Name::str(Name::mk_simple("Foo"), "Basic");
        let basic_env = loader.elaborate_module(&basic_name, base_env);
        assert!(basic_env.is_ok());

        // Check that Basic has access to Baz's definitions
        let basic_env = basic_env.unwrap();
        assert!(basic_env.contains(&hello_name)); // Imported from Baz
        let triple_name = Name::str(basic_name.clone(), "triple");
        assert!(basic_env.contains(&triple_name)); // Defined in Basic
    }

    #[test]
    fn test_import_cycle_detection() {
        let mut config = ModuleLoaderConfig::default();
        let loader = ModuleLoader::new(config.clone());

        // Simulate a cycle by marking a module as loading
        let test_name = Name::mk_simple("CycleTest");
        {
            let mut deps = loader.dependencies.lock().unwrap();
            deps.loading.insert(test_name.clone());
        }

        // Try to load the same module again
        let result = loader.load_module(&test_name);
        assert!(result.is_err());
        match result {
            Err(crate::error::ElabError::ImportCycle(name)) => {
                assert_eq!(name, test_name);
            }
            _ => panic!("Expected ImportCycle error"),
        }
    }

    #[test]
    fn test_module_caching() {
        let mut config = ModuleLoaderConfig::default();
        let project_root = std::env::current_dir().unwrap();
        config.search_paths.push(project_root.join("test/modules"));
        config.use_cache = true;

        let loader = ModuleLoader::new(config.clone());

        // Load a module
        let module_name = Name::str(Name::str(Name::mk_simple("Foo"), "Bar"), "Baz");
        let (module1, syntax1) = loader.load_module(&module_name).unwrap();

        // Load the same module again - should come from cache
        let (module2, syntax2) = loader.load_module(&module_name).unwrap();

        // Should be the same data
        assert_eq!(module1.name, module2.name);
        assert_eq!(module1.path, module2.path);
    }

    #[test]
    fn test_dependency_graph() {
        let mut config = ModuleLoaderConfig::default();
        let project_root = std::env::current_dir().unwrap();
        config.search_paths.push(project_root.join("test/modules"));

        let loader = ModuleLoader::new(config.clone());

        // Load modules to build dependency graph
        let baz_name = Name::str(Name::str(Name::mk_simple("Foo"), "Bar"), "Baz");
        let basic_name = Name::str(Name::mk_simple("Foo"), "Basic");

        loader.load_module(&baz_name).unwrap();
        loader.load_module(&basic_name).unwrap();

        // Check dependency relationships
        assert!(loader.has_dependency_path(&basic_name, &baz_name));
        assert!(!loader.has_dependency_path(&baz_name, &basic_name));

        // Get all dependencies of Basic
        let deps = loader.get_dependencies(&basic_name).unwrap();
        assert!(deps.contains(&baz_name));
    }
}