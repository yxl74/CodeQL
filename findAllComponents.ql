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

from AndroidManifestXmlFile manifest, AndroidComponentXmlElement component, string permNeeded, string permLevel
where 
  component.getFile() = manifest and
  permNeeded = component.getAttributeValue("permission") and
  (
    getPermissionLevel(manifest, permNeeded, permLevel)
    or
    (not getPermissionLevel(manifest, permNeeded, _) and
     permNeeded.matches("android.permission.%") and permLevel = "system")
    or
    (not getPermissionLevel(manifest, permNeeded, _) and
     not permNeeded.matches("android.permission.%") and permLevel = "Outside Current App")
  )
select
  component.getName() as componentType,
  component.getAttributeValue("name") as componentName,
  permNeeded as permissionNeeded,
  permLevel as permissionLevel
