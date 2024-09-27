import semmle.code.java.frameworks.android.Android
import semmle.code.xml.AndroidManifest

predicate getPermissionLevel(AndroidManifestXmlFile manifest, string permName, string permLevel) {
  exists(XmlElement permissionElement |
    permissionElement.getFile() = manifest and
    permissionElement.getName() = "permission" and
    permissionElement.getAttributeValue("name") = permName and
    permLevel = permissionElement.getAttributeValue("protectionLevel")
  )
}

from AndroidManifestXmlFile manifest, AndroidComponentXmlElement component, string permNeeded, string permLevel, string exported
where 
  component.getFile() = manifest and
  (
    permNeeded = component.getAttributeValue("permission")
    or
    not exists(component.getAttributeValue("permission")) and permNeeded = "None"
  ) and
  (
    // Case 1: No permission
    (permNeeded = "None" and permLevel = "N/A")
    or
    // Case 2: System permission
    (permNeeded.matches("android.permission.%") and permLevel = "System")
    or
    // Case 3: Permission defined in the app
    (getPermissionLevel(manifest, permNeeded, permLevel) and
     not permNeeded.matches("android.permission.%"))
    or
    // Case 4: Custom permission defined outside of the app
    (not permNeeded.matches("android.permission.%") and
     not getPermissionLevel(manifest, permNeeded, _) and
     permNeeded != "None" and
     permLevel = "Outside of app")
  ) and
  (
    exported = component.getAttributeValue("exported")
    or
    not exists(component.getAttributeValue("exported")) and exported = "false"
  )
select
  component.getName() as componentType,
  component.getAttributeValue("name") as componentName,
  exported as isExported,
  permNeeded as permissionNeeded,
  permLevel as permissionLevel
